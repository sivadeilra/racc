//! Implements LALR(1) analysis and table generation.
//!
//! See: [Efficient Computation of LALR(1) Look-Ahead Sets](http://3e8.org/pub/scheme/doc/parsing/Efficient%20Computation%20of%20LALR%281%29%20Look-Ahead%20Sets.pdf),
//! DeRemer and Pennello, ACM Transactions on Programming Languages and Systems.
//! 615–649. doi:10.1145/69622.357187
//!

use crate::grammar::Grammar;
use crate::lr0::LR0Output;
use crate::tvec::TVec;
use crate::util::Bitmat;
use crate::StateOrRule;
use crate::Symbol;
use crate::{Rule, State, Var};
use log::debug;
use ramp_table::RampTable;

/// The outputs of the `run_lalr_phase` function.
#[allow(non_snake_case)]
pub struct LALROutput {
    pub LA: Bitmat,
    pub gotos: GotoMap,
}

/// Describes a transition from one state to another state.
#[derive(Copy, Clone, Debug)]
pub struct Goto {
    pub(crate) from_state: State,
    pub(crate) to_state: State,
}

// Var -> [Goto]
pub type GotoMap = RampTable<Goto>;

#[allow(non_snake_case)]
pub(crate) fn run_lalr_phase(gram: &Grammar, lr0: &LR0Output) -> LALROutput {
    debug!("Running LALR phase");
    let gotos = set_goto_map(gram, lr0);
    let nullable = crate::lr0::set_nullable(gram);
    let mut F = initialize_F(gram, lr0, &nullable, &gotos);
    let (includes, lookback) = build_relations(gram, lr0, &nullable, &gotos);
    compute_FOLLOWS(&includes, &mut F);
    let LA = compute_lookaheads(gram, lr0, &lookback, &F);
    LALROutput { LA, gotos }
}

/// Builds the GotoMap: Var -> [FromTo]
///
/// For each symbol, we find the set of state transitions that this symbol can cause.
///
/// GotoMap::num_keys() = nvars
fn set_goto_map(gram: &Grammar, lr0: &LR0Output) -> GotoMap {
    debug!("set_goto_map");
    // Count the number of gotos for each variable.
    // Var -> count
    let mut goto_map: Vec<u32> = vec![0; gram.nvars + 1];
    let mut ngotos: usize = 0;

    // This code assumes that the entries in lr0.shifts[i] are ordered, such that
    // all token transitions precede all var transitions. This is true because
    // compute_lr0() sorts the shift list for each state.
    for shifts in lr0.shifts.iter() {
        for &state in shifts.iter().rev() {
            let symbol = lr0.accessing_symbol[state];
            if gram.is_token(symbol) {
                break;
            }
            assert!(ngotos < 0x7fff);
            ngotos += 1;
            goto_map[gram.symbol_to_var(symbol).index()] += 1;
        }
    }

    let ngotos = ngotos;

    // Next, we essentially "integrate" (in the numerical sense) goto_map.
    // Each entry is replaced with the sum of all previous entries.  The
    // original C code uses a temp_map to accomplish this, but it appears
    // that this could easily be done in place.
    let mut k: usize = 0;
    // Var -> index into goto_map
    let mut temp_map: Vec<u32> = Vec::with_capacity(gram.nvars + 1);
    for &g in goto_map[..gram.nvars].iter() {
        temp_map.push(k as u32);
        k += g as usize;
    }
    goto_map[..gram.nvars].copy_from_slice(&temp_map);

    goto_map[gram.nvars] = ngotos as u32;
    temp_map.push(ngotos as u32);
    // at this point, temp_map and goto_map have identical length and contents

    let mut from_to: Vec<Goto> = vec![
        Goto {
            from_state: State(0),
            to_state: State(0)
        };
        ngotos
    ];

    for (from_state, sp_shifts) in lr0.shifts.iter().enumerate() {
        let from_state = State(from_state as i16);
        for &to_state in sp_shifts.iter().rev() {
            let symbol = lr0.accessing_symbol[to_state];
            if gram.is_token(symbol) {
                break;
            }

            let k = &mut temp_map[gram.symbol_to_var(symbol).index()];
            from_to[*k as usize] = Goto {
                from_state,
                to_state,
            };
            *k += 1;
        }
    }

    let result = GotoMap {
        index: goto_map,
        values: from_to,
    };

    for (ivar, gotos) in result.iter().enumerate() {
        let var = Var(ivar as i16);
        let var_name = gram.name(gram.var_to_symbol(var));
        for goto in gotos.iter() {
            debug!(
                "goto[{:4}]  {:20} causes s{:-3} --> s{:-3}",
                result.index[ivar], var_name, goto.from_state, goto.to_state
            );
        }
    }

    result
}

/// Returns an index into goto_map, i.e. the "goto".
///
/// Searches the `GotoMap` for a state transition for `var` from state
/// `from_state`. Returns the index into the `GotoMap` for the given
/// transition.
fn map_goto(gotos: &GotoMap, from_state: State, var: Var) -> usize {
    use std::cmp::Ordering;
    let range = gotos.entry_values_range(var.index());
    let mut low = range.start;
    let mut high = range.end;
    loop {
        assert!(low < high);
        let middle = (low + high) / 2;
        match from_state.cmp(&gotos.all_values()[middle].from_state) {
            Ordering::Equal => return middle,
            Ordering::Less => high = middle,
            Ordering::Greater => low = middle + 1,
        }
    }
}

/// Builds the F relation. This relation is a `Bitmat`, whose rows correspond to "goto" indices
/// and whose columns correspond to token indices.
///
#[allow(non_snake_case)]
fn initialize_F(
    gram: &Grammar,
    lr0: &LR0Output,
    nullable: &TVec<Symbol, bool>,
    gotos: &GotoMap,
) -> Bitmat {
    debug!("initialize_F");

    let ngotos = gotos.num_values();
    let mut F = Bitmat::new(ngotos, gram.ntokens);
    let mut reads: Vec<Vec<i16>> = vec![vec![]; ngotos];

    // edge contains indices that point into GotoMap.
    // (In edge[i], i is not important.)
    let mut edge: Vec<i16> = Vec::new();

    for i in 0..ngotos {
        let stateno = gotos.all_values()[i].to_state;
        let shifts = &lr0.shifts[stateno.index()];

        if !shifts.is_empty() {
            let mut j: usize = 0;

            // Look at the tokens that shift to `stateno`.
            while j < shifts.len() {
                let symbol = lr0.accessing_symbol[shifts[j]];
                if gram.is_var(symbol) {
                    break;
                }
                // debug!("F(goto {}, {})", i, gram.name(symbol));
                F.set(i, symbol.index());
                j += 1;
            }

            while j < shifts.len() {
                let symbol = lr0.accessing_symbol[shifts[j]];
                if nullable[symbol] {
                    let mapped_goto = map_goto(gotos, stateno, gram.symbol_to_var(symbol));
                    debug!("    direct read: var {:-20}, mapped_goto {:4}, from_state {:4}, to_state {:4}",
                        gram.name(symbol),
                        mapped_goto,
                        stateno,
                        gotos.all_values()[mapped_goto].to_state,
                    );
                    edge.push(mapped_goto as i16);
                }
                j += 1;
            }

            if !edge.is_empty() {
                // debug!("state: {} has read edges: {:?}", stateno, edge);
                reads[i] = edge.to_vec();
                edge.clear();
            }
        }
    }

    F.set(0, 0);

    let F_before = F.clone();

    digraph(&reads, &mut F);

    debug!("initialize_F: Relation F, state transitions caused-by token:");
    for (goto_index, goto) in gotos.all_values().iter().enumerate() {
        for token_index in 0..F.cols {
            let token = Symbol(token_index as i16);

            let is_direct = F_before.get(goto_index, token_index);
            let is_trans = F.get(goto_index, token_index);
            assert!(
                implies(is_direct, is_trans),
                "direct should always imply trans: goto {}, {} --> {}, token {}",
                goto_index,
                goto.from_state,
                goto.to_state,
                gram.name(token)
            );

            if is_trans {
                debug!(
                    "    {:-4} --> {:-4}   caused by   {:-20}   {}",
                    goto.from_state,
                    goto.to_state,
                    gram.name(token),
                    if is_direct { "" } else { "transitive" },
                );
            }
        }
    }

    F
}

fn implies(p: bool, q: bool) -> bool {
    !p || q
}

/// Returns (includes, lookback)
///
/// The `includes` relation maps goto_index --> goto_index.
///
/// It is tempting to change the representation of `includes` to use a `Bitmat` or something similar.
/// However, so sayeth DeRemer:
///
/// > Watt's proposed bit matrix representations of the sparse relations reads and includes would be
/// > wasteful of space and time; for example, for a particular Ada grammar, each matrix contains
/// > almost five million bits.
///
/// What is needed is a SparseBitmat.
fn build_relations(
    gram: &Grammar,
    lr0: &LR0Output,
    nullable: &TVec<Symbol, bool>,
    gotos: &GotoMap,
) -> (Vec<Vec<StateOrRule>>, Vec<Vec<i16>>) {
    debug!("build_relations:");

    let ngotos = gotos.num_values();

    // includes maps goto_index --> StateOrRule
    let mut includes: Vec<Vec<StateOrRule>> = Vec::with_capacity(ngotos);

    let mut lookback: Vec<Vec<i16>> = vec![Vec::new(); lr0.reductions.num_values()];

    // Temporary tables, used only during this function.
    // These are cleared and reused many times.
    let mut states: Vec<State> = Vec::new();

    for (i, goto) in gotos.all_values().iter().enumerate() {
        let mut edge: Vec<StateOrRule> = Vec::new();
        assert!(states.is_empty());

        let from_state = goto.from_state;
        let symbol1 = lr0.accessing_symbol[goto.to_state];

        for &rule in &lr0.derives[gram.symbol_to_var(symbol1).index()] {
            assert!(states.is_empty());
            states.push(from_state);
            let mut stateno = from_state;
            for r in gram.rule_rhs_syms(rule).iter() {
                let symbol2 = r.as_symbol();
                for &shift in &lr0.shifts[stateno.index()] {
                    stateno = shift;
                    if lr0.accessing_symbol[stateno] == symbol2 {
                        break;
                    }
                }
                states.push(stateno);
            }

            add_lookback_edge(stateno, rule, i, &lr0.reductions, &mut lookback);

            let mut length = states.len() - 1;
            for r in gram.rule_rhs_syms(rule).iter().rev() {
                let gram_ritem = r.as_symbol();
                if !gram.is_var(gram_ritem) {
                    break;
                }
                length -= 1;
                edge.push(map_goto(gotos, states[length], gram.symbol_to_var(gram_ritem)) as i16);
                if !nullable[gram_ritem] || length == 0 {
                    break;
                }
            }
            states.clear(); // prepare for next use
        }
        includes.push(edge);
    }

    (transpose(&includes), lookback)
}

// Adds an entry to the 'lookback' table.
fn add_lookback_edge(
    state: State,
    ruleno: Rule,
    goto: usize,
    reductions: &RampTable<Rule>,
    lookback: &mut [Vec<i16>],
) {
    let range = reductions.entry_values_range(state.index());
    let state_rules = &reductions[state.index()];
    for (i, &r) in range.zip(state_rules) {
        if r == ruleno {
            lookback[i].insert(0, goto as i16);
            return;
        }
    }
    panic!("did not find rule");
}

#[allow(non_snake_case)]
fn transpose(r2: &[Vec<i16>]) -> Vec<Vec<i16>> {
    let mut nedges: Vec<i16> = vec![0; r2.len()];
    for sp in r2.iter() {
        for &e in sp.iter() {
            nedges[e as usize] += 1;
        }
    }

    let mut new_R: Vec<Vec<i16>> = nedges
        .iter()
        .map(|&n| Vec::with_capacity(n as usize))
        .collect();
    drop(nedges);

    for (i, sp) in r2.iter().enumerate() {
        // i is old-row
        for &k in sp.iter() {
            let k = k as usize;
            new_R[k].push(i as i16);
        }
    }

    new_R
}

#[allow(non_snake_case)]
fn compute_FOLLOWS(includes: &[Vec<i16>], F: &mut Bitmat) {
    digraph(includes, F);
}

#[allow(non_snake_case)]
fn compute_lookaheads(
    gram: &Grammar,
    lr0: &LR0Output,
    lookback: &[Vec<i16>],
    F: &Bitmat,
) -> Bitmat {
    let num_rules = lr0.reductions.num_values();
    let mut LA = Bitmat::new(num_rules, gram.ntokens);

    assert!(F.cols() == LA.cols());
    assert!(F.rowsize == LA.rowsize);

    for i in 0..num_rules {
        let fp3 = (i + 1) * LA.rowsize;
        for sp in lookback[i].iter() {
            let mut fp1 = i * LA.rowsize;
            let mut fp2 = (*sp as usize) * F.rowsize;
            while fp1 < fp3 {
                LA.data[fp1] |= F.data[fp2];
                fp1 += 1;
                fp2 += 1;
            }
        }
    }

    LA
}

// state for recursion
#[allow(non_snake_case)]
struct DigraphState<'a> {
    infinity: usize,
    index: Vec<i16>,
    vertices: Vec<i16>,
    top: usize,
    /// The "direct reads" relation.
    R: &'a [Vec<i16>],
    F: &'a mut Bitmat,
}

#[allow(non_snake_case)]
fn digraph(relation: &[Vec<i16>], F: &mut Bitmat) {
    let ngotos = F.rows();
    let mut ds = DigraphState {
        infinity: ngotos + 2,
        index: vec![0; ngotos + 1],
        vertices: vec![0; ngotos + 1],
        top: 0,
        R: relation,
        F,
    };

    for i in 0..ngotos {
        if ds.index[i] == 0 && !relation[i].is_empty() {
            traverse(&mut ds, i);
        }
    }
}

fn traverse(ds: &mut DigraphState<'_>, i: usize) {
    ds.top += 1;
    ds.vertices[ds.top] = i as i16;
    let height = ds.top;
    ds.index[i] = ds.top as i16;

    let base = i * ds.F.rowsize;
    let fp3 = base + ds.F.rowsize;

    for &j in ds.R[i].iter() {
        let j = j as usize;

        if ds.index[j] == 0 {
            traverse(ds, j);
        }

        if ds.index[i] > ds.index[j] {
            ds.index[i] = ds.index[j];
        }

        let mut fp1 = base;
        let mut fp2 = j * ds.F.rowsize;

        while fp1 < fp3 {
            ds.F.data[fp1] |= ds.F.data[fp2];
            fp1 += 1;
            fp2 += 1;
        }
    }

    if (ds.index[i] as usize) == height {
        loop {
            let j = ds.vertices[ds.top] as usize;
            ds.top -= 1;
            ds.index[j] = ds.infinity as i16;

            if i == j {
                break;
            }

            let mut fp1 = base;
            let mut fp2 = j * ds.F.rowsize;

            while fp1 < fp3 {
                ds.F.data[fp2] = ds.F.data[fp1];
                fp1 += 1;
                fp2 += 1;
            }
        }
    }
}
