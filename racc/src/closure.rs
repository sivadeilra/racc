use crate::grammar::Grammar;
use crate::lr0::DerivesTable;
use crate::util::{word_size, Bitmat, Bitv32};
use crate::warshall::reflexive_transitive_closure;
use crate::{Item, Rule, Var};
use log::debug;

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
    nrules: usize,
    rule_set: &mut Bitv32,
    item_set: &mut Vec<Item>,
)
{
    assert!(item_set.len() == 0);

    let rulesetsize = word_size(nrules);

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
