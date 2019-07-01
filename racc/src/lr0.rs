use crate::closure::closure;
use crate::closure::set_first_derives;
use crate::grammar::Grammar;
use crate::util::Bitv32;
use crate::ramp_table::{RampTable, RampTableBuilder};
use crate::{Rule, State, Item};
use crate::tvec::TVec;
use log::debug;

use crate::aliases::Symbol;

pub const INITIAL_STATE_SYMBOL: Symbol = Symbol(0);

// State -> [Item]
type CoreTable = RampTable<Item>;

pub struct LR0Output {
    pub nstates: usize,

    // index: State
    // value: Symbol
    pub accessing_symbol: TVec<State, Symbol>,

    /// Contains (state -> [state]) mappings for shifts
    pub shifts: RampTable<State>,

    pub reductions: Reductions,
    pub derives: DerivesTable,
}

// num_keys = number of states
// items = rules
pub type Reductions = RampTable<Rule>;

impl LR0Output {
    pub fn nstates(&self) -> usize {
        self.nstates
    }
}

struct KernelTable {
    base: Vec<i16>, // values in this array are indexes into the KernelTable::items array
    items: Vec<Item>,
}

fn sort_shift_symbols(shift_symbol: &mut [Symbol]) {
    // this appears to be a bubble-sort of shift_symbol?
    for i in 1..shift_symbol.len() {
        let symbol = shift_symbol[i];
        let mut j = i;
        while j > 0 && shift_symbol[j - 1] > symbol {
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
        items: vec![0; kernel_items_count],
    };

    // values in this array are indexes into the KernelTable::items array
    let mut kernels_end: Vec<i16> = vec![-1; gram.nsyms];

    let mut states = CoreTable::new();
    let mut accessing_symbol: TVec<State, Symbol> = TVec::new();

    // This function creates the initial state, using the DERIVES relation for
    // the start symbol.  From this initial state, we will discover / create all
    // other states, by examining a state, the next variables that could be
    // encountered in those states, and finding the transitive closure over same.
    // Initializes the state table.
    states.push_entry(derives.values(gram.start_symbol).iter().map(|&item| gram.rrhs[item as usize]));
    accessing_symbol.push(INITIAL_STATE_SYMBOL);

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
    let mut shift_symbol: Vec<Symbol> = Vec::new();

    // this_state represents our position within our work list.  The output.states
    // array represents both our final output, and this_state is the next state
    // within that array, where we need to generate new states from.  New states
    // are added to output.states within find_or_create_state() (called below).
    let mut this_state: usize = 0;

    // State which becomes the output
    let mut reductions = RampTableBuilder::<Rule>::new();
    let mut shifts = RampTableBuilder::<State>::new();

    while this_state < states.num_keys() {
        assert!(item_set.len() == 0);
        debug!("computing closure for state s{}:", this_state);
        print_core(gram, this_state as State, states.values(this_state as usize));

        // The output of closure() is stored in item_set.
        // rule_set is used only as temporary storage.
        // debug!("    nucleus items: {}", &lr0.states[this_state].items);
        closure(
            gram,
            &states.values(this_state as usize),
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
        new_item_sets(&kernels.base, &mut kernels.items, &mut kernels_end, gram, &item_set, &mut shift_symbol);

        // Find or create states for shifts in the current state.  This can potentially add new
        // states to 'states'.  Then record the resulting shifts in 'shifts'.
        shifts.start_key();
        if !shift_symbol.is_empty() {
            sort_shift_symbols(&mut shift_symbol);
            for &symbol in shift_symbol.iter() {
                let symbol_items = &kernels.items[kernels.base[symbol.0 as usize] as usize..kernels_end[symbol.0 as usize] as usize];
                let shift_state =
                    find_or_create_state(gram, symbol_items, &mut state_set, &mut states, &mut accessing_symbol, symbol);
                shifts.push_value(shift_state);
            }
        }

        item_set.clear();
        shift_symbol.clear();

        debug!("");
        this_state += 1;
    }

    let nstates = states.num_keys();

    // finish the states table
    states.index.push(states.table.len());

    LR0Output {
        nstates: nstates,
        accessing_symbol,
        reductions: reductions.finish(),
        shifts: shifts.finish(),
        derives,
    }
}

// Gets the state for a particular symbol.  If no appropriate state exists,
// then a new state will be created.
fn find_or_create_state(
    gram: &Grammar,
    symbol_items: &[Item],
    state_set: &mut [Vec<State>],
    states: &mut CoreTable,
    accessing_symbol: &mut TVec<State, Symbol>,
    symbol: Symbol,
) -> State {
    let key_item = symbol_items[0] as usize; // key is an item index, in [0..nitems).
    let this_state_set = &mut state_set[key_item];

    // Search for an existing Core that has the same items.
    for &state in this_state_set.iter() {
        if symbol_items == states.values(state as usize) {
            return state as i16;
        }
    }

    // No match.  Add a new entry to the list.

    assert!(states.num_keys() < 0x7fff);

    let new_state = states.num_keys() as State;

    for &symbol_item in symbol_items {
        states.push_value(symbol_item);
    }
    states.finish_key();
    accessing_symbol.push(symbol);

    // Add the new state to the state set for this symbol.
    this_state_set.push(new_state);

    debug!("    created state s{}:", new_state);
    print_core(gram, new_state, symbol_items);

    new_state
}

fn print_core(gram: &Grammar, state: State, items: &[Item]) {
    // debug!("    s{} : accessing_symbol={}", state, gram.name[core.accessing_symbol as usize]);
    debug!("    s{}", state);

    let mut line = String::new();
    for i in 0..items.len() {
        let rhs = items[i] as usize;
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
    kernels_base: &[Item],
    kernels_items: &mut [Item],
    kernels_end: &mut [i16],
    gram: &Grammar,
    item_set: &[Item],
    shift_symbol: &mut Vec<Symbol>,
) {
    assert!(shift_symbol.len() == 0);

    // reset kernel_end
    for i in kernels_end.iter_mut() {
        *i = -1;
    }

    for &item in item_set.iter() {
        let symbol = gram.ritem[item as usize];
        if symbol > 0 {
            let mut ksp = kernels_end[symbol as usize];
            if ksp == -1 {
                shift_symbol.push(Symbol(symbol));
                ksp = kernels_base[symbol as usize];
            }
            kernels_items[ksp as usize] = (item + 1) as i16;
            kernels_end[symbol as usize] = ksp + 1;
        }
    }
}

/// Examine the items in the given item set.  If any of the items have reached the
/// end of the rhs list for a particular rule, then add that rule to the reduction set.
/// We discover this by testing the sign of the next symbol in the item; if it is
/// negative, then we have reached the end of the symbols on the rhs of a rule.  See
/// the code in reader::pack_grammar(), where this information is set up.
fn save_reductions(gram: &Grammar, item_set: &[Item], rules: &mut RampTableBuilder<Rule>) {
    for &i in item_set {
        let item = gram.ritem[i as usize];
        if item < 0 {
            rules.push_value(-item);
        }
    }
}

// maps from Symbol -> [Rule]
pub type DerivesTable = RampTable<Rule>;

// Computes the "derives" and "derives_rules" arrays.
fn set_derives(gram: &Grammar) -> DerivesTable {
    // note: 'derives' appears to waste its token space; consider adjusting indices
    // so that only var indices are used
    let mut d = RampTableBuilder::<Rule>::with_capacity(gram.nsyms, gram.nvars + gram.nrules);
    for _ in 0..gram.start_symbol {
        d.start_key();
    }
    for lhs in gram.start_symbol..gram.nsyms {
        d.start_key();
        for r in 0..gram.nrules {
            if gram.rlhs[r] as usize == lhs {
                d.push_value(r as Rule);
            }
        }
    }

    let derives = d.finish();
    print_derives(gram, &derives);
    derives
}

fn print_derives(gram: &Grammar, derives: &DerivesTable) {
    debug!("DERIVES:");
    for lhs in gram.start_symbol..gram.nsyms {
        debug!("    {} derives rules: ", gram.name[lhs]);
        for &rule in derives.values(lhs) {
            debug!("        {}", &gram.rule_to_str(rule));
        }
    }
}

pub fn set_nullable(gram: &Grammar) -> TVec<Symbol, bool> {
    let mut nullable: Vec<bool> = vec![false; gram.nsyms];

    loop {
        let mut done = true;
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
                let sym = gram.rlhs[(-j) as usize];
                if !nullable[sym as usize] {
                    nullable[sym as usize] = true;
                    done = false;
                }
            }
            i += 1;
        }
        if done {
            break;
        }
    }

    for i in gram.start_symbol..gram.nsyms {
        let sym = i;
        if nullable[sym] {
            debug!("{} is nullable", gram.name[i]);
        } else {
            debug!("{} is not nullable", gram.name[i]);
        }
    }

    TVec::from_vec(nullable)
}
