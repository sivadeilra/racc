use grammar::Grammar;
use closure::set_first_derives;
use closure::closure;
use util::Bitv32;
use std::collections::Bitv;
use std::iter::repeat;

/// the structure of the LR(0) state machine
pub struct Core
{
    pub accessing_symbol: usize,
    pub items: Vec<i16>,
}

/// The structure used to record shifts
pub struct Shifts
{
    pub state: usize,
    pub shifts: Vec<i16>,
}

/// the structure used to store reductions
pub struct Reductions
{
    pub state: usize,
    pub rules: Vec<i16>,
}

#[derive(Default)]
pub struct LR0Output
{
    pub states: Vec<Core>,
    pub shifts: Vec<Shifts>,
    pub reductions: Vec<Reductions>,
    pub nullable: Bitv,
    pub derives: Vec<i16>,
    pub derives_rules: Vec<i16>
}

impl LR0Output
{
    pub fn nstates(&self) -> usize {
        self.states.len()
    }
}

// intermediate variables for LR(0)
struct LR0State<'a>
{
    gram: &'a Grammar,

    // Contains the set of states that are relevant for each item.  Each entry in this
    // table corresponds to an item, so state_set.len() = nitems.  The contents of each
    // entry is a list of state indices (into LR0Output.states).
    state_set: Vec<Vec<usize>>, 
    
    states: Vec<Core>,

    kernel_base: Vec<i16>,      // values in this array are indexes into the kernel_items array    
    kernel_end: Vec<i16>,       // values in this array are indexes into the kernel_items array
    kernel_items: Vec<i16>,
}

fn sort_shift_symbols(shift_symbol: &mut [i16]) {
    // this appears to be a bubble-sort of shift_symbol?
    for i in 1 .. shift_symbol.len() {
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
    let (derives, derives_rules) = set_derives(gram);

    // was: allocate_item_sets()
    // This defines LR0State fields: kernel_base, kernel_items, kernel_end, shift_symbol
    // The kernel_* fields are allocated to well-defined sizes, but their contents are
    // not well-defined yet.
    let mut kernel_items_count: usize = 0;
    let mut symbol_count: Vec<i16> = repeat(0).take(gram.nsyms).collect();
    for i in range(0, gram.nitems) {
        let symbol = gram.ritem[i];
        if symbol >= 0 {
            kernel_items_count += 1;
            symbol_count[symbol as usize] += 1;
        }
    }
    let kernel_base = {
        let mut kernel_base: Vec<i16> = repeat(0).take(gram.nsyms).collect();
        let mut count: usize = 0;
        for i in range(0, gram.nsyms) {
            kernel_base[i] = count as i16;
            count += symbol_count[i] as usize;
        }
        kernel_base
    };

    let mut lr0: LR0State = LR0State {
        gram: gram,
        state_set: range(0, gram.nitems).map(|_| Vec::new()).collect(),
        kernel_base: kernel_base,
        kernel_end: repeat(-1).take(gram.nsyms).collect(),
        kernel_items: repeat(0).take(kernel_items_count).collect(),
        states: initialize_states(gram, derives.as_slice(), derives_rules.as_slice())
    };

    let first_derives = set_first_derives(gram, derives.as_slice(), derives_rules.as_slice());

    // These vectors are used for building tables during each state.
    // It is inefficient to allocate and free these vectors within
    // the scope of processing each state.
    let mut item_set: Vec<i16> = Vec::with_capacity(gram.nitems);
    let mut rule_set: Bitv32 = Bitv32::from_elem(gram.nrules, false);
    let mut shift_symbol: Vec<i16> = Vec::new();

    // this_state represents our position within our work list.  The output.states
    // array represents both our final output, and this_state is the next state
    // within that array, where we need to generate new states from.  New states
    // are added to output.states within get_state() (called below).
    let mut this_state: usize = 0;

    // State which becomes the output
    let mut reductions: Vec<Reductions> = Vec::new();
    let mut shifts: Vec<Shifts> = Vec::new();

    while this_state < lr0.states.len() {
        assert!(item_set.len() == 0);
        debug!("computing closure for state s{}:", this_state);
        print_core(gram, this_state, &lr0.states[this_state]);

        // The output of closure() is stored in item_set.
        // rule_set is used only as temporary storage.
        // debug!("    nucleus items: {}", lr0.states[this_state].items.as_slice());
        closure(gram, &lr0.states[this_state].items[], &first_derives, gram.nrules, &mut rule_set, &mut item_set);

        // The output of save_reductions() is stored in reductions.
        save_reductions(gram, this_state, &item_set[], &mut reductions);

        // new_item_sets updates kernel_items, kernel_end, and shift_symbol, and also
        // computes (returns) the number of shifts for the current state.
        debug!("    new_item_sets: item_set = {:?}", item_set);
        new_item_sets(gram, &mut lr0, &item_set[], &mut shift_symbol);
        sort_shift_symbols(&mut shift_symbol[]);

        // Find or create states for shifts in the current state.  This can potentially add new
        // states to lr0.states.  Then record the resulting shifts in 'shifts'.
        if shift_symbol.len() > 0 {
            let shift_set: Vec<i16> = shift_symbol.iter().map(|&mut: symbol| get_state(&mut lr0, *symbol as usize) as i16).collect();
            debug!("    shifts: {:?}", shift_set);
            shifts.push(Shifts {
                state: this_state,
                shifts: shift_set
            });
        }

        item_set.clear();
        shift_symbol.clear();

        debug!("");
        this_state += 1;
    }

    // Return results
    LR0Output {
        states: lr0.states,
        reductions: reductions,
        shifts: shifts,
        nullable: set_nullable(gram),
        derives: derives,
        derives_rules: derives_rules
    }
}

// Gets the state for a particular symbol.  If no appropriate state exists,
// then a new state will be created.
fn get_state(lr0: &mut LR0State, symbol: usize) -> usize {
    let isp = lr0.kernel_base[symbol] as usize;
    let iend = lr0.kernel_end[symbol] as usize;
    let n = iend - isp;

    let key = lr0.kernel_items[isp] as usize; // key is an item index, in [0..nitems).

    // Search for an existing Core that has the same items.
    for &state in lr0.state_set[key].iter() {
        let sp_items = &lr0.states[state].items;
        if sp_items.len() == n {
            let mut found = true;
            for j in range(0, n) {
                if lr0.kernel_items[isp + j] != sp_items[j] {
                    found = false;
                    break;
                }
            }
            if found {
                // We found an existing state with the same items.
                return state;
            }
        }
    }

    // No match.  Add a new entry to the list.

    assert!(lr0.states.len() < 0x7fff);

    let new_state = lr0.states.len();
    lr0.states.push(Core {
        accessing_symbol: symbol,
        items: vec_from_slice(&lr0.kernel_items[lr0.kernel_base[symbol] as usize .. lr0.kernel_end[symbol] as usize])
    });

    // Add the new state to the state set for this symbol.
    lr0.state_set[key].push(new_state);

    debug!("    created state s{}:", new_state);
    print_core(lr0.gram, new_state, &lr0.states[new_state]);

    new_state
}

// This function creates the initial state, using the DERIVES relation for
// the start symbol.  From this initial state, we will discover / create all
// other states, by examining a state, the next variables that could be
// encountered in those states, and finding the transitive closure over same.
// Initializes the state table.
fn initialize_states(gram: &Grammar, derives: &[i16], derives_rules: &[i16]) -> Vec<Core> {
    debug!("initialize_states");

    let start_derives: usize = derives[gram.start_symbol] as usize;

    // measure the number of items in the initial state, so we can
    // allocate a vector of the exact size.
    let mut core_nitems: usize = 0;
    while derives_rules[start_derives + core_nitems] >= 0 {
        core_nitems += 1;
    }

    // create the initial state
    let mut states: Vec<Core> = Vec::new();
    states.push(Core {
        items: {
            let mut items = Vec::with_capacity(core_nitems);
            let mut i: usize = 0;
            while derives_rules[start_derives + i] >= 0 {
                items.push(gram.rrhs[derives_rules[start_derives + i] as usize]);
                i += 1;
            }
            items
        },
        accessing_symbol: 0
    });

    debug!("initial state:");
    print_core(gram, 0, &states[0]);

    states
}

fn print_core(gram: &Grammar, state: usize, core: &Core) {
    debug!("    s{} : accessing_symbol={}", state, gram.name[core.accessing_symbol]);

    let mut line = String::new();
    for i in range(0, core.items.len()) {
        let rhs = core.items[i] as usize;
        line.push_str(format!("item {:4} : ", rhs).as_slice());

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
            line.push(' ');
            line.push_str(gram.name[gram.ritem[j] as usize].as_slice());
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
fn new_item_sets(gram: &Grammar, lr0: &mut LR0State, item_set: &[i16], shift_symbol: &mut Vec<i16>) {
    assert!(shift_symbol.len() == 0);

    // reset kernel_end
    for i in lr0.kernel_end.iter_mut() {
        *i = -1;
    }

    for &it in item_set.iter() {
        let symbol = gram.ritem[it as usize];
        if symbol > 0 {
            let mut ksp = lr0.kernel_end[symbol as usize];
            if ksp == -1 {
                shift_symbol.push(symbol);
                ksp = lr0.kernel_base[symbol as usize];
            }

            lr0.kernel_items[ksp as usize] = (it + 1) as i16;
            ksp += 1;
            lr0.kernel_end[symbol as usize] = ksp;
        }
    }
}

fn save_reductions(gram: &Grammar, this_state: usize, item_set: &[i16], reductions: &mut Vec<Reductions>) {
    // Examine the items in the given item set.  If any of the items have reached the
    // end of the rhs list for a particular rule, then add that rule to the reduction set.
    // We discover this by testing the sign of the next symbol in the item; if it is
    // negative, then we have reached the end of the symbols on the rhs of a rule.  See
    // the code in reader::pack_grammar(), where this information is set up.
    let red_count = item_set.iter().filter(|&&i| gram.ritem[i as usize] < 0).count();
    if red_count != 0 {
        reductions.push(Reductions {
            state: this_state,
            rules: {
                let mut rules: Vec<i16> = Vec::with_capacity(red_count);
                rules.extend(item_set.iter()
                    .map(|&i| gram.ritem[i as usize])
                    .filter(|&item| item < 0)
                    .map(|item| {
                        let rule = -item;
                        debug!("        reduction: r{}  {}", rule, gram.rule_to_str(rule as usize));
                        rule
                    }));
                rules
            }
        });
    }
    else {
        debug!("    no reductions");
    }
}

// Computes the "derives" and "derives_rules" arrays.
fn set_derives(gram: &Grammar) -> (Vec<i16>, Vec<i16>) // (derives, derives_rules)
{
    // note: 'derives' appears to waste its token space; consider adjusting indices
    // so that only var indices are used
	let mut derives: Vec<i16> = repeat(0).take(gram.nsyms).collect();
    let mut derives_rules: Vec<i16> = Vec::with_capacity(gram.nvars + gram.nrules);

    for lhs in range(gram.start_symbol, gram.nsyms) {
        derives[lhs] = derives_rules.len() as i16;
        for r in range(0, gram.nrules) {
            if gram.rlhs[r] as usize == lhs {
                derives_rules.push(r as i16);
            }
        }
        derives_rules.push(-1);
    }

    print_derives(gram, derives.as_slice(), derives_rules.as_slice());

    (derives, derives_rules)
}

fn print_derives(gram: &Grammar, derives: &[i16], derives_rules: &[i16])
{
    debug!("");
    debug!("DERIVES:");
    debug!("");

    for lhs in range(gram.start_symbol, gram.nsyms) {
        debug!("    {} derives rules: ", gram.name[lhs]);
        let mut sp = derives[lhs] as usize;
        while derives_rules[sp] >= 0 {
            let r = derives_rules[sp] as usize;
            debug!("        {}", gram.rule_to_str(r).as_slice());
            sp += 1;
        }
    }
    debug!("");
}

fn set_nullable(gram: &Grammar) -> Bitv
{
    let mut nullable = Bitv::from_elem(gram.nsyms, false);

    let mut done_flag = false;
    while !done_flag {
        done_flag = true;
        let mut i = 1;
        while i < gram.nitems {
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
                    nullable.set(j as usize, true);
                    done_flag = false;
                }
            }
        	i += 1;
        }
    }

    for i in range(gram.start_symbol, gram.nsyms) {
        if nullable[i] {
            debug!("{} is nullable", gram.name[i]);
        }
        else {
            debug!("{} is not nullable", gram.name[i]);
        }
    }

    nullable
}

fn vec_from_slice<T:Clone>(s: &[T]) -> Vec<T>
{
	let mut v = Vec::with_capacity(s.len());
	v.push_all(s);
	v
}
