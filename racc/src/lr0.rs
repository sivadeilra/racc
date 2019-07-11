use crate::grammar::Grammar;
use crate::ramp_table::{RampTable, RampTableBuilder};
use crate::tvec::TVec;
use crate::util::word_size;
use crate::util::Bitmat;
use crate::util::Bitv32;
use crate::warshall::reflexive_transitive_closure;
use crate::{Item, Rule, State, Var};
use log::debug;

use crate::Symbol;

pub const INITIAL_STATE_SYMBOL: Symbol = Symbol(0);

// State -> [Item]
type CoreTable = RampTable<Item>;

pub struct LR0Output {
    pub nstates: usize,

    // index: State
    // value: Symbol
    pub accessing_symbol: TVec<State, Symbol>,

    /// Contains (State -> [State]) mappings for shifts
    pub shifts: RampTable<State>,

    /// Contains State -> [Rule]
    pub reductions: Reductions,

    /// Contains Symbol -> [Rule]
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

pub fn compute_lr0(gram: &Grammar) -> LR0Output {
    let derives = set_derives(gram);

    // was: allocate_item_sets()
    // This defines: kernel_base, kernel_items, kernel_end, shift_symbol
    // The kernel_* fields are allocated to well-defined sizes, but their contents are
    // not well-defined yet.
    let mut kernel_items_count: usize = 0;
    let mut symbol_count: Vec<usize> = vec![0; gram.nsyms];
    for &symbol in gram.ritem.iter() {
        if symbol.is_symbol() {
            let symbol = symbol.as_symbol();
            kernel_items_count += 1;
            symbol_count[symbol.index()] += 1;
        }
    }
    let mut kernel_base: Vec<usize> = vec![0; gram.nsyms];
    let mut count: usize = 0;
    for i in 0..gram.nsyms {
        kernel_base[i] = count;
        count += symbol_count[i];
    }
    let mut kernel_items: Vec<Item> = vec![Item(0); kernel_items_count];

    // values in this array are indexes into kernel_base
    let mut kernel_end: Vec<usize> = vec![0; gram.nsyms];

    let mut states = CoreTable::new();
    let mut accessing_symbol: TVec<State, Symbol> = TVec::new();

    // This function creates the initial state, using the DERIVES relation for
    // the start symbol.  From this initial state, we will discover / create all
    // other states, by examining a state, the next variables that could be
    // encountered in those states, and finding the transitive closure over same.
    // Initializes the state table.
    states.push_entry(
        derives
            .values(gram.symbol_to_var(gram.start()))
            .iter()
            .map(|&item| gram.rrhs(item)),
    );
    accessing_symbol.push(INITIAL_STATE_SYMBOL);

    // Contains the set of states that are relevant for each item.  Each entry in this
    // table corresponds to an item, so state_set.len() = nitems.  The contents of each
    // entry is a list of state indices (into LR0Output.states).
    // Item -> [State]
    let mut state_set: Vec<Vec<State>> = vec![vec![]; gram.nitems()];

    let first_derives = set_first_derives(gram, &derives);

    // These vectors are used for building tables during each state.
    // It is inefficient to allocate and free these vectors within
    // the scope of processing each state.
    let mut item_set: Vec<Item> = Vec::with_capacity(gram.nitems());
    let mut rule_set: Bitv32 = Bitv32::from_elem(gram.nrules, false);
    let mut shift_symbol: Vec<Symbol> = Vec::new();

    // this_state represents our position within our work list.  The output.states
    // array represents both our final output, and this_state is the next state
    // within that array, where we need to generate new states from.  New states
    // are added to output.states within find_or_create_state() (called below).
    let mut this_state: usize = 0;

    // State which becomes the output
    let mut reductions = RampTable::<Rule>::new();
    let mut shifts = RampTable::<State>::new();

    while this_state < states.num_keys() {
        assert!(item_set.len() == 0);
        debug!("computing closure for state s{}:", this_state);
        print_core(gram, State(this_state as i16), states.values(this_state));

        // The output of closure() is stored in item_set.
        // rule_set is used only as temporary storage.
        closure(
            gram,
            &states.values(this_state),
            &first_derives,
            &mut rule_set,
            &mut item_set,
        );

        // The output of save_reductions() is stored in reductions.
        save_reductions(gram, &item_set, &mut reductions);

        new_item_sets(
            &kernel_base,
            &mut kernel_items,
            &mut kernel_end,
            gram,
            &item_set,
            &mut shift_symbol,
        );

        // Find or create states for shifts in the current state.  This can potentially add new
        // states to 'states'.  Then record the resulting shifts in 'shifts'.
        shift_symbol.sort();
        for &symbol in shift_symbol.iter() {
            let shift_state = find_or_create_state(
                gram,
                &kernel_items[kernel_base[symbol.index()]..kernel_end[symbol.index()]],
                &mut state_set,
                &mut states,
                &mut accessing_symbol,
                symbol,
            );
            shifts.push_value(shift_state);
        }
        shifts.finish_key();

        item_set.clear();
        shift_symbol.clear();
        this_state += 1;
    }

    let nstates = states.num_keys();

    LR0Output {
        nstates,
        accessing_symbol,
        reductions,
        shifts,
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
    let key_item = symbol_items[0];
    let this_state_set = &mut state_set[key_item.index()];

    // Search for an existing Core that has the same items.
    for &state in this_state_set.iter() {
        if symbol_items == states.values(state) {
            return state;
        }
    }

    // No match.  Add a new entry to the list.
    let new_state: State = states.num_keys().into();
    states.push_entry_copy_slice(symbol_items);
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
        let rhs = items[i].index();
        line.push_str(&format!("item {:4} : ", rhs));

        // back up to start of this rule
        let mut rhs_first = rhs;
        while rhs_first > 0 && gram.ritem[rhs_first - 1].is_symbol() {
            rhs_first -= 1;
        }

        // loop through rhs
        let mut j = rhs_first;
        while gram.ritem[j].is_symbol() {
            let s = gram.ritem[j].as_symbol();
            if j == rhs {
                line.push_str(" .");
            }
            line.push_str(&format!(" {}", gram.name(s)));
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
// kernel_base: Symbol -> index into kernel_items
// kernel_end: Symbol -> index into kernel_items
fn new_item_sets(
    kernel_base: &[usize],
    kernel_items: &mut [Item],
    kernel_end: &mut [usize],
    gram: &Grammar,
    item_set: &[Item],
    shift_symbol: &mut Vec<Symbol>,
) {
    assert!(shift_symbol.len() == 0);

    // reset kernel_end
    kernel_end.copy_from_slice(kernel_base);

    for &item in item_set.iter() {
        let symbol = gram.ritem(item);
        if symbol.is_symbol() {
            let symbol = symbol.as_symbol();
            let base = kernel_base[symbol.index()];
            let end = &mut kernel_end[symbol.index()];
            if *end == base {
                shift_symbol.push(symbol);
            }
            kernel_items[*end] = item + 1;
            *end += 1;
        }
    }
}

/// Examine the items in the given item set.  If any of the items have reached the
/// end of the rhs list for a particular rule, then add that rule to the reduction set.
/// We discover this by testing the sign of the next symbol in the item; if it is
/// negative, then we have reached the end of the symbols on the rhs of a rule.  See
/// the code in reader::pack_grammar(), where this information is set up.
fn save_reductions(gram: &Grammar, item_set: &[Item], rules: &mut RampTable<Rule>) {
    for &item in item_set {
        let sr = gram.ritem(item);
        if sr.is_rule() {
            rules.push_value(sr.as_rule());
        }
    }
    rules.finish_key();
}

// maps from Symbol -> [Rule]
pub type DerivesTable = RampTable<Rule>;

/// Compute the DERIVES table. The DERIVES table maps Var -> [Rule].
fn set_derives(gram: &Grammar) -> DerivesTable {
    let mut d = RampTableBuilder::<Rule>::with_capacity(gram.nsyms, gram.nvars + gram.nrules);
    for lhs in gram.iter_var_syms() {
        d.start_key();
        for rule in gram.iter_rules() {
            if gram.rlhs(rule) == lhs {
                d.push_value(rule as Rule);
            }
        }
    }

    let derives = d.finish();
    print_derives(gram, &derives);
    derives
}

fn print_derives(gram: &Grammar, derives: &DerivesTable) {
    debug!("DERIVES:");
    for lhs in gram.iter_vars() {
        let lhs_sym = gram.var_to_symbol(lhs);
        debug!("    {} derives rules: ", gram.name(lhs_sym));
        for &rule in derives.values(lhs) {
            debug!("        {}", &gram.rule_to_str(rule));
        }
    }
}

pub fn set_nullable(gram: &Grammar) -> TVec<Symbol, bool> {
    let mut nullable: TVec<Symbol, bool> = TVec::from_vec(vec![false; gram.nsyms]);
    loop {
        let mut done = true;
        let mut i = 1;
        while i < gram.ritem.len() {
            let mut empty = true;
            let rule = loop {
                let sr = gram.ritem[i];
                if sr.is_rule() {
                    break sr.as_rule();
                }
                let sym = sr.as_symbol();
                if !nullable[sym] {
                    empty = false;
                }
                i += 1;
            };
            if empty {
                let sym = gram.rlhs(rule);
                if !nullable[sym] {
                    nullable[sym] = true;
                    done = false;
                }
            }
            i += 1;
        }
        if done {
            break;
        }
    }

    for sym in gram.iter_var_syms() {
        if nullable[sym] {
            debug!("{} is nullable", gram.name(sym));
        } else {
            debug!("{} is not nullable", gram.name(sym));
        }
    }

    nullable
}

/// Computes the "epsilon-free firsts" (EFF) relation.
/// The EFF is a bit matrix [nvars, nvars].
fn set_eff(gram: &Grammar, derives: &DerivesTable) -> Bitmat {
    let nvars = gram.nvars;
    let mut eff: Bitmat = Bitmat::new(nvars, nvars);
    for row in 0..nvars {
        for &rule in derives.values(row) {
            let symbol = gram.ritem(gram.rrhs(rule)).as_symbol();
            if gram.is_var(symbol) {
                eff.set(row, gram.symbol_to_var(symbol).0 as usize);
            }
        }
    }

    reflexive_transitive_closure(&mut eff);
    print_eff(gram, &eff);
    eff
}

/// Returns the first_derives relation, which is a bit matrix of size [nvars, nrules].
/// Each row corresponds to a variable, and each column corresponds to a rule.
///
/// Note: Because this relation is only relevant to variables (non-terminals), the table
/// does not waste space on tokens.  That is, row 0 is assigned to the first non-terminal
/// (Grammar.start_symbol).  So when indexing using a symbol value, you have to subtract
/// start_symbol (or, equivalently, ntokens) first.
///
/// This implementation processes bits in groups of 32, for the sake of efficiency.
/// It is not clear whether this complexity is still justifiable, but it is preserved.
pub fn set_first_derives(gram: &Grammar, derives: &DerivesTable) -> Bitmat {
    // Compute EFF, which is a [nvars, nvars] bit matrix
    let eff = set_eff(gram, derives);
    assert!(eff.rows == gram.nvars);
    assert!(eff.cols == gram.nvars);
    let mut first_derives = Bitmat::new(gram.nvars, gram.nrules);
    for (i, j) in eff.iter_ones() {
        for &rule in derives.values(j) {
            first_derives.set(i, rule.index());
        }
    }

    print_first_derives(gram, &first_derives);
    first_derives
}

// Computes the closure of a set of item sets, and writes the result into 'item_set'.
// nucleus contains a set of items, that is, positions within reductions that are possible
// in the current state.  The closure() function looks at the next symbol in each item, and
// if the next symbol is a variable, the first_derives relation is consulted in order to see
// which other rules need to be added to the closure.
//
// The caller provides a mutable rule_set array, which is guaranteed to hold enough space for
// a bit vector of size nrules.  The caller does not otherwise use rule_set; the caller provides
// rule_set only to avoid frequently allocating and destroying an array.
//
// Similarly, the item_set is passed as a mutable vector.  However, the caller guarantees that
// item_set will be empty on call to closure(), and closure() writes its output into item_set.
//
// * rule_set: bit vector, size=nrules; temporary data, written and read by this fn
//
// TODO: Consider changing item_set from Vec<Item> to a bitmap, whose length is nitems.
// Then the 'states' table becomes a Bitmat.
pub fn closure(
    gram: &Grammar,
    nucleus: &[Item],
    first_derives: &Bitmat,
    rule_set: &mut Bitv32,
    item_set: &mut Vec<Item>,
) {
    assert!(item_set.len() == 0);

    let rulesetsize = word_size(rule_set.nbits);

    // clear rule_set
    rule_set.set_all(false);

    // For each item in the nucleus, examine the next symbol in the item.
    // If the next symbol is a non-terminal, then find the corresponding
    // row in the first_derives table, and merge that row into the rule_set
    // bit vector.  The result is that rule_set will contain a bit vector
    // that identifies the rules need to be added to the closure of the
    // current state.  Keep in mind that we process bit vectors in u32 chunks.
    for &item in nucleus.iter() {
        let symbol_or_rule = gram.ritem(item);
        if symbol_or_rule.is_symbol() {
            let symbol = symbol_or_rule.as_symbol();
            if gram.is_var(symbol) {
                let var = gram.symbol_to_var(symbol);
                let dsp = var.index() * first_derives.rowsize;
                for i in 0..rulesetsize {
                    rule_set.data[i] |= first_derives.data[dsp + i];
                }
            }
        }
    }

    // Scan the rule_set that we just constructed. The rule_set tells us which
    // items need to be merged into the item set for the item set. Thus,
    // new_items = nucleus merged with rule_set.iter_ones().
    //
    // This code relies on this invariant:
    //      for all r: gram.rrhs[r + 1] > gram.rrhs[r]
    let mut i: usize = 0; // index into nucleus
    for rule in rule_set.iter_ones() {
        let item = gram.rrhs[rule];
        while i < nucleus.len() && nucleus[i] < item {
            item_set.push(nucleus[i]);
            i += 1;
        }
        item_set.push(item);
        while i < nucleus.len() && nucleus[i] == item {
            i += 1;
        }
    }

    while i < nucleus.len() {
        item_set.push(nucleus[i]);
        i += 1;
    }
}

fn print_eff(gram: &Grammar, eff: &Bitmat) {
    debug!("Epsilon Free Firsts");
    for i in 0..eff.rows {
        let var = Var(i as i16);
        debug!("{}", gram.name(gram.var_to_symbol(var)));
        for j in eff.iter_ones_in_row(i) {
            debug!("  {}", gram.name(gram.var_to_symbol(Var(j as i16))));
        }
    }
}

// first_derives: cols = nrules
fn print_first_derives(gram: &Grammar, first_derives: &Bitmat) {
    debug!("");
    debug!("First Derives");
    debug!("");
    for i in 0..gram.nvars {
        let var = Var(i as i16);
        debug!("{} derives:", gram.name(gram.var_to_symbol(var)));
        for j in first_derives.iter_ones_in_row(i) {
            debug!("    {}", gram.rule_to_str(Rule(j as i16)));
        }
    }
}
