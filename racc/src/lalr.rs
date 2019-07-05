use crate::grammar::Grammar;
use crate::lr0::{LR0Output, Reductions};
use crate::ramp_table::RampTable;
use crate::tvec::TVec;
use crate::util::Bitmat;
use crate::StateOrRule;
use crate::Symbol;
use crate::{Rule, State};
use log::debug;

#[allow(non_snake_case)]
pub struct LALROutput {
    pub LA: Bitmat,
    pub gotos: GotoMap,
}

#[derive(Copy, Clone, Debug)]
pub struct FromTo {
    pub from_state: State,
    pub to_state: State,
}

// Var -> [FromTo]
pub type GotoMap = RampTable<FromTo>;

#[allow(non_snake_case)]
pub fn run_lalr(gram: &Grammar, lr0: &LR0Output) -> LALROutput {
    let gotos = set_goto_map(gram, lr0);
    let nullable = crate::lr0::set_nullable(gram);
    let mut F = initialize_F(gram, lr0, &nullable, &gotos);
    let (includes, lookback) = build_relations(gram, lr0, &nullable, &gotos);
    compute_FOLLOWS(&includes, &mut F);
    let LA = compute_lookaheads(gram, lr0, &lookback, &F);
    LALROutput { LA, gotos }
}

// Finds the longest rhs
fn set_max_rhs(gram: &Grammar) -> usize {
    let mut length: usize = 0;
    let mut max: usize = 0;
    for &item in gram.ritem.iter() {
        if item.is_symbol() {
            length += 1;
        } else {
            if length > max {
                max = length;
            }
            length = 0;
        }
    }
    max
}

/// Builds the GotoMap: Var -> [FromTo]
///
/// GotoMap::num_keys() = nvars
fn set_goto_map(gram: &Grammar, lr0: &LR0Output) -> GotoMap {
    // Count the number of gotos for each variable.
    // Var -> count
    let mut goto_map: Vec<usize> = vec![0; gram.nvars + 1];
    let mut ngotos: usize = 0;

    for shifts in lr0.shifts.iter_entries() {
        for i in (0..shifts.len()).rev() {
            let state = shifts[i];
            let symbol = lr0.accessing_symbol[state];
            if gram.is_token(symbol) {
                break;
            }
            assert!(ngotos < 0x7fff);
            ngotos += 1;
            goto_map[gram.symbol_to_var(symbol).0 as usize] += 1;
        }
    }

    let ngotos = ngotos;

    // Next, we essentially "integrate" (in the numerical sense) goto_map.
    // Each entry is replaced with the sum of all previous entries.  The
    // original C code uses a temp_map to accomplish this, but it appears
    // that this could easily be done in place.
    let mut k: usize = 0;
    // Var -> index into goto_map
    let mut temp_map: Vec<usize> = Vec::with_capacity(gram.nvars + 1);
    for i in 0..gram.nvars {
        temp_map.push(k);
        k += goto_map[i];
    }
    for i in 0..gram.nvars {
        goto_map[i] = temp_map[i];
    }

    goto_map[gram.nvars] = ngotos;
    temp_map.push(ngotos);
    // at this point, temp_map and goto_map have identical length and contents

    let mut from_to: Vec<FromTo> = vec![
        FromTo {
            from_state: State(0),
            to_state: State(0)
        };
        ngotos
    ];

    for (sp_state, sp_shifts) in lr0.shifts.iter_sets() {
        let sp_state = State(sp_state as i16);
        for &state2 in sp_shifts.iter().rev() {
            let symbol = lr0.accessing_symbol[state2];
            if gram.is_token(symbol) {
                break;
            }

            let k = temp_map[symbol.0 as usize - gram.ntokens] as usize;
            temp_map[symbol.0 as usize - gram.ntokens] += 1;
            from_to[k] = FromTo {
                from_state: sp_state,
                to_state: state2,
            };
        }
    }

    /*
        debug!("set_goto_map: ngotos={}", ngotos);
        for i in 0..ngotos {
            debug!("    from {:3} to {:3}", from_state[i], to_state[i]);
        }

        debug!("goto_map:");
        for i in 0..gram.nvars {
            debug!(
                "    {:3} {} --> {}",
                i,
                gram.name[i + gram.ntokens],
                goto_map[i]
            );
        }
        debug!(".");
    */

    GotoMap {
        index: goto_map,
        table: from_to,
    }
}

// Returns an index into goto_map, i.e. the "goto".
fn map_goto(gram: &Grammar, gotos: &GotoMap, state: State, symbol: Symbol) -> usize {
    let var = gram.symbol_to_var(symbol);
    let range = gotos.values_range(var);
    let mut low = range.start;
    let mut high = range.end;
    loop {
        assert!(low < high);
        let middle = (low + high) / 2;
        let s = gotos.value(middle).from_state;
        if s == state {
            return middle;
        }
        if s < state {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
}

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
    let mut edge: Vec<i16> = Vec::with_capacity(ngotos + 1);

    for i in 0..ngotos {
        let stateno = gotos.table[i].to_state;
        let shifts = lr0.shifts.values(stateno.0 as usize);

        if !shifts.is_empty() {
            let mut j: usize = 0;
            while j < shifts.len() {
                let symbol = lr0.accessing_symbol[shifts[j]];
                if gram.is_var(symbol) {
                    break;
                }
                F.set(i, symbol.0 as usize);
                j += 1;
            }

            while j < shifts.len() {
                let symbol = lr0.accessing_symbol[shifts[j]];
                if nullable[symbol] {
                    edge.push(map_goto(gram, gotos, stateno, symbol) as i16);
                }
                j += 1;
            }

            if edge.len() != 0 {
                let mut rp: Vec<i16> = Vec::with_capacity(edge.len() + 1);
                rp.reserve_exact(edge.len() + 1);
                rp.extend(&edge);
                rp.push(-1);
                reads[i] = rp;
                edge.clear();
            }
        }
    }

    F.set(0, 0);
    digraph(&reads, &mut F);
    F
}

// Returns (includes, lookback)
fn build_relations(
    gram: &Grammar,
    lr0: &LR0Output,
    nullable: &TVec<Symbol, bool>,
    gotos: &GotoMap,
) -> (Vec<Vec<StateOrRule>>, Vec<Vec<i16>>) {
    let ngotos = gotos.num_values();
    let mut includes: Vec<Vec<StateOrRule>> = Vec::with_capacity(ngotos);
    let mut lookback: Vec<Vec<i16>> = vec![Vec::new(); lr0.reductions.num_values()];

    // Temporary tables, used only during this function.
    // These are cleared and reused many times.
    let mut states: Vec<State> = Vec::with_capacity(set_max_rhs(gram) + 1);

    for i in 0..ngotos {
        let mut edge: Vec<StateOrRule> = Vec::new();
        assert!(states.len() == 0);

        let goto = gotos.value(i);
        let from_state = goto.from_state;
        let symbol1 = lr0.accessing_symbol[goto.to_state];

        for &rule in lr0.derives.values(gram.symbol_to_var(symbol1)) {
            assert!(states.len() == 0);
            states.push(from_state);
            let mut stateno = from_state;
            let rule_rhs = gram.rule_rhs_syms(rule);
            let mut rp: usize = 0; // index into rule_rhs
            while rp < rule_rhs.len() {
                let symbol2 = rule_rhs[rp].as_symbol();
                for &shift in lr0.shifts.values(stateno) {
                    stateno = shift;
                    if lr0.accessing_symbol[stateno] == symbol2 {
                        break;
                    }
                }

                states.push(stateno);
                rp += 1;
            }

            add_lookback_edge(stateno, rule, i, &lr0.reductions, &mut lookback);

            let mut length = states.len() - 1;
            while rp > 0 {
                rp -= 1;
                let gram_ritem = rule_rhs[rp].as_symbol();
                if !gram.is_var(gram_ritem) {
                    break;
                }
                length -= 1;
                edge.push(map_goto(gram, gotos, states[length], gram_ritem) as i16);
                if !nullable[gram_ritem] || length == 0 {
                    break;
                }
            }
            states.clear(); // prepare for next use
        }

        if !edge.is_empty() {
            edge.push(-1);
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
    reductions: &Reductions,
    lookback: &mut Vec<Vec<i16>>,
) {
    let range = reductions.values_range(state);
    let state_rules = reductions.values(state);
    for (i, &r) in range.clone().zip(state_rules) {
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
    for i in 0..r2.len() {
        let sp = &r2[i];
        if sp.len() > 0 {
            let mut j: usize = 0;
            while sp[j] >= 0 {
                let e = sp[j] as usize;
                j += 1;
                nedges[e] += 1;
            }
        }
    }

    let mut new_R: Vec<Vec<i16>> = vec![Vec::new(); r2.len()];

    for i in 0..r2.len() {
        let k = nedges[i];
        if k > 0 {
            let mut sp: Vec<i16> = vec![0; (k as usize) + 1];
            sp[k as usize] = -1;
            new_R[i] = sp;
        }
    }
    drop(nedges);

    let mut temp_R: Vec<i16> = vec![0; r2.len()]; // contains output columns
    for i in 0..r2.len() {
        // i is old-row
        let sp = &r2[i];
        let mut j: usize = 0; // j is old-col
        if sp.len() > 0 {
            while sp[j] >= 0 {
                let k = sp[j] as usize;
                j += 1;

                let out_col = temp_R[k];
                temp_R[k] += 1;

                new_R[k][out_col as usize] = i as i16;
            }
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

    assert!(F.cols == LA.cols);
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
    R: &'a [Vec<i16>],
    F: &'a mut Bitmat,
}

#[allow(non_snake_case)]
fn digraph(relation: &[Vec<i16>], F: &mut Bitmat) {
    let ngotos = F.rows;
    let mut ds = DigraphState {
        infinity: ngotos + 2,
        index: vec![0; ngotos + 1],
        vertices: vec![0; ngotos + 1],
        top: 0,
        R: relation,
        F: F,
    };

    for i in 0..ngotos {
        if ds.index[i] == 0 && relation[i].len() != 0 {
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

    if ds.R[i].len() != 0 {
        let rp = &ds.R[i];
        let mut rpi: usize = 0;
        loop {
            let j = rp[rpi];
            rpi += 1;
            if j < 0 {
                break;
            }
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
