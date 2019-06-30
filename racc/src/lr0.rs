use crate::closure::closure;
use crate::closure::set_first_derives;
use crate::grammar::Grammar;
use crate::util::Bitv32;
use crate::util::{RampTable, RampTableBuilder};
use crate::{Rule, State, Symbol, Item};
use log::debug;

/// the structure of the LR(0) state machine
pub struct Core {
    pub accessing_symbol: Symbol,
    pub items: Vec<i16>,
}

pub struct LR0Output {
    pub states: Vec<Core>,

    /// Contains (state -> [state]) mappings for shifts
    pub shifts: RampTable<State>,

    pub reductions: Reductions,
    pub nullable: Vec<bool>,
    pub derives: DerivesTable,
}

// num_keys = number of states
// items = rules
pub type Reductions = RampTable<Rule>;

impl LR0Output {
    pub fn nstates(&self) -> usize {
        self.states.len()
    }
}

struct KernelTable {
    base: Vec<i16>, // values in this array are indexes into the KernelTable::items array
    end: Vec<i16>,  // values in this array are indexes into the KernelTable::items array
    items: Vec<i16>,
}
impl KernelTable {
    pub fn items_for_symbol(&self, symbol: i16) -> &[i16] {
        let start = self.base[symbol as usize] as usize;
        let end = self.end[symbol as usize] as usize;
        &self.items[start..end]
    }
}

fn sort_shift_symbols(shift_symbol: &mut [i16]) {
    // this appears to be a bubble-sort of shift_symbol?
    for i in 1..shift_symbol.len() {
        let symbol = shift_symbol[i];
        let mut j = i;
        while j > 0 && (shift_symbol[j - 1]) > symbol {
            shift_symbol[j] = shift_symbol[j - 1];
            j -= 1;
        }
        shift_symbol[j] = symbol;
    }
}

pub fn compute_lr0(gram: &Grammar) -> LR0Output {
    let derives = set_derives(gram);

    // was: allocate_item_sets()
    // This defines: kernel_base, kernel_items, kernel_end, shift_symbol
    // The kernel_* fields are allocated to well-defined sizes, but their contents are
    // not well-defined yet.
    let mut kernel_items_count: usize = 0;
    let mut symbol_count: Vec<i16> = vec![0; gram.nsyms];
    for &symbol in gram.ritem.iter() {
        if symbol >= 0 {
            kernel_items_count += 1;
            symbol_count[symbol as usize] += 1;
        }
    }
    let mut kernels = KernelTable {
        base: {
            let mut kernel_base: Vec<i16> = vec![0; gram.nsyms];
            let mut count: usize = 0;
            for i in 0..gram.nsyms {
                kernel_base[i] = count as i16;
                count += symbol_count[i] as usize;
            }
            kernel_base
        },
        end: vec![-1; gram.nsyms],
        items: vec![0; kernel_items_count],
    };

    let mut states = initialize_states(gram, &derives);
    // Contains the set of states that are relevant for each item.  Each entry in this
    // table corresponds to an item, so state_set.len() = nitems.  The contents of each
    // entry is a list of state indices (into LR0Output.states).
    let mut state_set: Vec<Vec<State>> = vec![vec![]; gram.nitems()];

    let first_derives = set_first_derives(gram, &derives);

    // These vectors are used for building tables during each state.
    // It is inefficient to allocate and free these vectors within
    // the scope of processing each state.
    let mut item_set: Vec<i16> = Vec::with_capacity(gram.nitems());
    let mut rule_set: Bitv32 = Bitv32::from_elem(gram.nrules, false);
    let mut shift_symbol: Vec<i16> = Vec::new();

    // this_state represents our position within our work list.  The output.states
    // array represents both our final output, and this_state is the next state
    // within that array, where we need to generate new states from.  New states
    // are added to output.states within find_or_create_state() (called below).
    let mut this_state: usize = 0;

    // State which becomes the output
    let mut reductions = RampTableBuilder::<Rule>::new();
    let mut shifts = RampTableBuilder::<State>::new();

    while this_state < states.len() {
        assert!(item_set.len() == 0);
        debug!("computing closure for state s{}:", this_state);
        print_core(gram, this_state as State, &states[this_state]);

        // The output of closure() is stored in item_set.
        // rule_set is used only as temporary storage.
        // debug!("    nucleus items: {}", &lr0.states[this_state].items);
        closure(
            gram,
            &states[this_state].items,
            &first_derives,
            gram.nrules,
            &mut rule_set,
            &mut item_set,
        );

        // The output of save_reductions() is stored in reductions.
        reductions.start_key();
        save_reductions(gram, &item_set, &mut reductions);

        // new_item_sets updates kernel_items, kernel_end, and shift_symbol, and also
        // computes (returns) the number of shifts for the current state.
        debug!("    new_item_sets: item_set = {:?}", item_set);
        new_item_sets(&mut kernels, gram, &item_set, &mut shift_symbol);

        // Find or create states for shifts in the current state.  This can potentially add new
        // states to 'states'.  Then record the resulting shifts in 'shifts'.
        shifts.start_key();
        if !shift_symbol.is_empty() {
            sort_shift_symbols(&mut shift_symbol);
            for &symbol in shift_symbol.iter() {
                let symbol_items = kernels.items_for_symbol(symbol);
                let shift_state =
                    find_or_create_state(gram, symbol_items, &mut state_set, &mut states, symbol);
                shifts.push_value(shift_state);
            }
        }

        item_set.clear();
        shift_symbol.clear();

        debug!("");
        this_state += 1;
    }

    // Return results
    LR0Output {
        states,
        reductions: reductions.finish(),
        shifts: shifts.finish(),
        nullable: set_nullable(gram),
        derives,
    }
}

// Gets the state for a particular symbol.  If no appropriate state exists,
// then a new state will be created.
fn find_or_create_state(
    gram: &Grammar,
    symbol_items: &[Item],
    state_set: &mut [Vec<State>],
    states: &mut Vec<Core>,
    symbol: Symbol,
) -> State {
    let key_item = symbol_items[0] as usize; // key is an item index, in [0..nitems).
    let this_state_set = &mut state_set[key_item];

    // Search for an existing Core that has the same items.
    for &state in this_state_set.iter() {
        if symbol_items == states[state as usize].items.as_slice() {
            return state as i16;
        }
    }

    // No match.  Add a new entry to the list.

    assert!(states.len() < 0x7fff);

    let new_state = states.len() as State;
    states.push(Core {
        accessing_symbol: symbol,
        items: symbol_items.to_vec(),
    });

    // Add the new state to the state set for this symbol.
    this_state_set.push(new_state);

    debug!("    created state s{}:", new_state);
    print_core(gram, new_state, states.last().as_ref().unwrap());

    new_state
}

// This function creates the initial state, using the DERIVES relation for
// the start symbol.  From this initial state, we will discover / create all
// other states, by examining a state, the next variables that could be
// encountered in those states, and finding the transitive closure over same.
// Initializes the state table.
fn initialize_states(gram: &Grammar, d: &DerivesTable) -> Vec<Core> {
    debug!("initialize_states");

    let start_derives: usize = d.derives[gram.start_symbol] as usize;

    // measure the number of items in the initial state, so we can
    // allocate a vector of the exact size.
    let mut core_nitems: usize = 0;
    while d.derives_rules[start_derives + core_nitems] >= 0 {
        core_nitems += 1;
    }

    // create the initial state
    let mut states: Vec<Core> = Vec::new();
    states.push(Core {
        items: {
            let mut items = Vec::with_capacity(core_nitems);
            for i in 0.. {
                let item = d.derives_rules[start_derives + i];
                if item < 0 {
                    break;
                }
                items.push(gram.rrhs[item as usize]);
            }
            items
        },
        accessing_symbol: 0,
    });

    debug!("initial state:");
    print_core(gram, 0, &states[0]);

    states
}

fn print_core(gram: &Grammar, state: State, core: &Core) {
    debug!(
        "    s{} : accessing_symbol={}",
        state, gram.name[core.accessing_symbol as usize]
    );

    let mut line = String::new();
    for i in 0..core.items.len() {
        let rhs = core.items[i] as usize;
        line.push_str(&format!("item {:4} : ", rhs));

        // back up to start of this rule
        let mut rhs_first = rhs;
        while rhs_first > 0 && gram.ritem[rhs_first - 1] >= 0 {
            rhs_first -= 1;
        }

        // loop through rhs
        let mut j = rhs_first;
        while gram.ritem[j] >= 0 {
            if j == rhs {
                line.push_str(" .");
            }
            line.push_str(&format!(" {}", gram.name[gram.ritem[j] as usize]));
            j += 1;
        }
        if j == rhs {
            line.push_str(" .");
        }

        debug!("        {}", line);
        line.clear();
    }
}

// fills shift_symbol with shifts
fn new_item_sets(
    kernels: &mut KernelTable,
    gram: &Grammar,
    item_set: &[i16],
    shift_symbol: &mut Vec<i16>,
) {
    assert!(shift_symbol.len() == 0);

    // reset kernel_end
    for i in kernels.end.iter_mut() {
        *i = -1;
    }

    for &it in item_set.iter() {
        let symbol = gram.ritem[it as usize];
        if symbol > 0 {
            let mut ksp = kernels.end[symbol as usize];
            if ksp == -1 {
                shift_symbol.push(symbol);
                ksp = kernels.base[symbol as usize];
            }

            kernels.items[ksp as usize] = (it + 1) as i16;
            ksp += 1;
            kernels.end[symbol as usize] = ksp;
        }
    }
}

/// Examine the items in the given item set.  If any of the items have reached the
/// end of the rhs list for a particular rule, then add that rule to the reduction set.
/// We discover this by testing the sign of the next symbol in the item; if it is
/// negative, then we have reached the end of the symbols on the rhs of a rule.  See
/// the code in reader::pack_grammar(), where this information is set up.
fn save_reductions(gram: &Grammar, item_set: &[i16], rules: &mut RampTableBuilder<Rule>) {
    for &i in item_set {
        let item = gram.ritem[i as usize];
        if item < 0 {
            rules.push_value(-item);
        }
    }
}

pub struct DerivesTable {
    // index is a Symbol.
    // value is an index into  derives_rules
    pub derives: Vec<i16>,
    pub derives_rules: Vec<Rule>    
}

// Computes the "derives" and "derives_rules" arrays.
fn set_derives(gram: &Grammar) -> DerivesTable {
    // note: 'derives' appears to waste its token space; consider adjusting indices
    // so that only var indices are used
    let mut d = DerivesTable {
        derives: vec![0; gram.nsyms],
        derives_rules: Vec::with_capacity(gram.nvars + gram.nrules)
    };

    for lhs in gram.start_symbol..gram.nsyms {
        d.derives[lhs] = d.derives_rules.len() as i16;
        for r in 0..gram.nrules {
            if gram.rlhs[r] as usize == lhs {
                d.derives_rules.push(r as Rule);
            }
        }
        d.derives_rules.push(-1);
    }

    print_derives(gram, &d);
    d
}

fn print_derives(gram: &Grammar, d: &DerivesTable) {
    debug!("DERIVES:");
    for lhs in gram.start_symbol..gram.nsyms {
        debug!("    {} derives rules: ", gram.name[lhs]);
        let mut sp = d.derives[lhs] as usize;
        while d.derives_rules[sp] >= 0 {
            let r = d.derives_rules[sp] as usize;
            debug!("        {}", &gram.rule_to_str(r));
            sp += 1;
        }
    }
}

pub fn set_nullable(gram: &Grammar) -> Vec<bool> {
    let mut nullable: Vec<bool> = vec![false; gram.nsyms];

    let mut done_flag = false;
    while !done_flag {
        done_flag = true;
        let mut i = 1;
        while i < gram.ritem.len() {
            let mut empty = true;
            let mut j: i16;
            loop {
                j = gram.ritem[i];
                if j < 0 {
                    break;
                }
                if !nullable[j as usize] {
                    empty = false;
                }
                i += 1;
            }
            if empty {
                j = gram.rlhs[(-j) as usize];
                if !nullable[j as usize] {
                    nullable[j as usize] = true;
                    done_flag = false;
                }
            }
            i += 1;
        }
    }

    for i in gram.start_symbol..gram.nsyms {
        if nullable[i] {
            debug!("{} is nullable", gram.name[i]);
        } else {
            debug!("{} is not nullable", gram.name[i]);
        }
    }

    nullable
}
