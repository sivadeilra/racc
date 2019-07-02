use crate::Symbol;
use crate::lr0::DerivesTable;
use crate::grammar::Grammar;
use crate::util::{word_size, Bitmat, Bitv32};
use crate::warshall::reflexive_transitive_closure;
use crate::Item;
use log::debug;

/// Computes the "epsilon-free firsts" (EFF) relation.
/// The EFF is a bit matrix [nvars, nvars].
fn set_eff(gram: &Grammar, derives: &DerivesTable) -> Bitmat {
    let nvars = gram.nvars;
    let mut eff: Bitmat = Bitmat::new(nvars, nvars);
    for row in 0..nvars {
        for &rule in derives.values(gram.start_symbol + row) {
            let symbol = gram.ritem[gram.rrhs[rule as usize] as usize].as_symbol();
            if gram.is_var(symbol) {
                eff.set(row, symbol.0 as usize - gram.start_symbol);
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

    let mut first_derives = Bitmat::new(gram.nvars, gram.nrules);

    /* known good, old
    for i in range(0, gram.nvars) {
        let mut vrow = i * eff.rowsize;     // used to read cols for an eff row, j is column
        let mut cword: u32 = 0;
        let mut k = BITS_PER_WORD;
        for jvar in range(0, gram.nvars) {
            let j = gram.start_symbol + jvar;
            if k >= BITS_PER_WORD {
                cword = eff.data[vrow];
                vrow += 1;
                k = 0;
            }

            if (cword & (1u32 << k)) != 0 {
                let mut rp = derives[j] as usize;
                while derives_rules[rp] >= 0 {
                    first_derives.set(i, derives_rules[rp] as usize);
                    rp += 1;
                }
            }

            k += 1; // advance to next bit
        }
    }
        */

    /* this works! iter based
    for i in range(0, gram.nvars) {
        for j in eff.iter_ones_in_row(i) {
            let mut rp = derives[gram.start_symbol + j] as usize;
            while derives_rules[rp] >= 0 {
                first_derives.set(i, derives_rules[rp] as usize);
                rp += 1;
            }
        }
    } */

    assert!(eff.rows == gram.nvars);
    assert!(eff.cols == gram.nvars);
    for (i, j) in eff.iter_ones() {
        for &rule in derives.values(gram.start_symbol + j) {
            first_derives.set(i, rule as usize);
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
pub fn closure(
    gram: &Grammar,
    nucleus: &[Item],
    first_derives: &Bitmat,
    nrules: usize,
    rule_set: &mut Bitv32, // bit vector, size=nrules; temporary data, written and read by this fn
    item_set: &mut Vec<i16>,
) // output is written to this vec
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
    for &ni in nucleus.iter() {
        assert!(ni >= 0);
        let symbol = gram.ritem[ni as usize];
        if symbol.is_symbol() && gram.is_var(symbol.as_symbol()) {
            let dsp: usize = ((symbol.as_symbol().0 as usize) - gram.ntokens) * first_derives.rowsize;
            for i in 0..rulesetsize {
                rule_set.data[i] |= first_derives.data[dsp + i];
            }
        }
    }

    // Scan the rule_set that we just constructed.
    let mut csp: usize = 0;
    for r in rule_set.iter_ones() {
        let itemno = gram.rrhs[r];
        while csp < nucleus.len() && nucleus[csp] < itemno {
            item_set.push(nucleus[csp]);
            csp += 1;
        }
        item_set.push(itemno as i16);
        while csp < nucleus.len() && nucleus[csp] == itemno {
            csp += 1;
        }
    }

    while csp < nucleus.len() {
        item_set.push(nucleus[csp]);
        csp += 1;
    }
}

fn print_eff(gram: &Grammar, eff: &Bitmat) {
    debug!("Epsilon Free Firsts");
    for i in 0..eff.rows {
        debug!("{}", gram.name[gram.start_symbol + i]);
        for j in eff.iter_ones_in_row(i) {
            let s: usize = gram.start_symbol + j;
            debug!("  {}", gram.name[s]);
        }
    }
}

// first_derives: cols = nrules
fn print_first_derives(gram: &Grammar, first_derives: &Bitmat) {
    debug!("");
    debug!("First Derives");
    debug!("");
    for i in 0..gram.nvars {
        debug!("{} derives:", gram.name[gram.start_symbol + i]);
        for j in first_derives.iter_ones_in_row(i) {
            debug!("    {}", rule_to_string(gram, j));
        }
    }
}

fn rule_to_string(gram: &Grammar, rule: usize) -> String {
    let mut result = String::new();
    let rlhs = gram.rlhs[rule];
    result.push_str(&format!("(r{}) {} : ", rule, gram.name(rlhs)));

    for i in gram.rrhs[rule]..gram.rrhs[rule + 1] - 1 {
        let rhs = gram.ritem[i as usize];
        result.push_str(&format!(" {}", gram.name(rhs.as_symbol())));
    }
    result
}
