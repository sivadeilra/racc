use crate::grammar::Grammar;
use crate::lr0::{LR0Output, Reductions};
use crate::util::Bitmat;
use crate::{Rule, State};
use log::debug;

#[allow(non_snake_case)]
pub struct LALROutput {
    pub LA: Bitmat,
    pub gotos: GotoMap,
}

pub struct GotoMap {
    pub ngotos: usize,
    pub goto_map: Vec<i16>,
    pub from_state: Vec<i16>,
    pub to_state: Vec<i16>,
}

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
        if item >= 0 {
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

fn set_goto_map(gram: &Grammar, lr0: &LR0Output) -> GotoMap {
    // Count the number of gotos for each variable.
    let mut goto_map: Vec<i16> = vec![0; gram.nvars + 1];
    let mut ngotos: usize = 0;

    for shifts in lr0.shifts.iter_values() {
        for i in (0..shifts.len()).rev() {
            let state = shifts[i] as usize;
            let symbol = lr0.states[state].accessing_symbol;

            if gram.is_token(symbol) {
                break;
            }
            assert!(ngotos < 0x7fff);
            ngotos += 1;
            goto_map[symbol as usize - gram.ntokens] += 1;
        }
    }

    let ngotos = ngotos;

    // Next, we essentially "integrate" (in the numerical sense) goto_map.
    // Each entry is replaced with the sum of all previous entries.  The
    // original C code uses a temp_map to accomplish this, but it appears
    // that this could easily be done in place.
    let mut k: i16 = 0;
    let mut temp_map: Vec<i16> = Vec::with_capacity(gram.nvars + 1);
    for i in 0..gram.nvars {
        temp_map.push(k);
        k += goto_map[i];
    }
    for i in 0..gram.nvars {
        goto_map[i] = temp_map[i];
    }

    goto_map[gram.nvars] = ngotos as i16;
    temp_map.push(ngotos as i16);
    // at this point, temp_map and goto_map have identical length and contents

    let mut from_state: Vec<i16> = vec![0; ngotos];
    let mut to_state: Vec<i16> = vec![0; ngotos];

    for (sp_state, sp_shifts) in lr0.shifts.iter_sets() {
        for &state2 in sp_shifts.iter().rev() {
            let symbol = lr0.states[state2 as usize].accessing_symbol;
            if gram.is_token(symbol) {
                break;
            }

            let k = temp_map[symbol as usize - gram.ntokens] as usize;
            temp_map[symbol as usize - gram.ntokens] += 1;
            from_state[k] = sp_state as State;
            to_state[k] = state2;
        }
    }

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

    GotoMap {
        ngotos: ngotos,
        goto_map: goto_map,
        from_state: from_state,
        to_state: to_state,
    }
}

// returns an index into goto_map
fn map_goto(gram: &Grammar, gotos: &GotoMap, state: usize, symbol: i16) -> usize {
    let symbol = symbol as usize;
    let var = symbol - gram.ntokens;
    let init_low = gotos.goto_map[var] as usize;
    let init_high = gotos.goto_map[var + 1] as usize;
    let mut low = init_low;
    let mut high = init_high;

    loop {
        assert!(low <= high);
        let middle = (low + high) >> 1;
        let s = gotos.from_state[middle] as usize;
        if s == state {
            return middle;
        }
        if s < state {
            low = middle + 1;
        } else {
            high = middle - 1;
        }
    }
}

#[allow(non_snake_case)]
fn initialize_F(gram: &Grammar, lr0: &LR0Output, nullable: &[bool], gotos: &GotoMap) -> Bitmat {
    debug!("initialize_F");

    let ngotos = gotos.ngotos;
    let mut F = Bitmat::new(ngotos, gram.ntokens);
    let mut reads: Vec<Vec<i16>> = vec![vec![]; ngotos];
    let mut edge: Vec<i16> = Vec::with_capacity(ngotos + 1);

    for i in 0..ngotos {
        let stateno = gotos.to_state[i] as usize;
        let shifts = lr0.shifts.values(stateno);

        if !shifts.is_empty() {
            let mut j: usize = 0;
            while j < shifts.len() {
                let symbol = lr0.states[shifts[j] as usize].accessing_symbol;
                if gram.is_var(symbol) {
                    break;
                }
                F.set(i, symbol as usize);
                j += 1;
            }

            while j < shifts.len() {
                let symbol = lr0.states[shifts[j] as usize].accessing_symbol;
                if nullable[symbol as usize] {
                    let e = map_goto(gram, gotos, stateno, symbol);
                    edge.push(e as i16);
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

fn build_relations(
    gram: &Grammar,
    lr0: &LR0Output,
    nullable: &[bool],
    gotos: &GotoMap,
) -> (Vec<Vec<i16>>, /*lookback:*/ Vec<Vec<i16>>) {
    debug!("build_relations");

    let ngotos = gotos.ngotos;
    let mut includes: Vec<Vec<i16>> = vec![Vec::new(); ngotos];
    let mut edge: Vec<i16> = Vec::with_capacity(ngotos + 1); // temporary, reused in loops
    let mut states: Vec<i16> = Vec::with_capacity(set_max_rhs(gram) + 1); // temporary, reused in loops
    let mut lookback: Vec<Vec<i16>> = vec![Vec::new(); lr0.reductions.num_values()];

    for i in 0..ngotos {
        assert!(edge.len() == 0);
        assert!(states.len() == 0);

        let state1 = gotos.from_state[i] as usize;
        let symbol1 = lr0.states[gotos.to_state[i] as usize].accessing_symbol as usize;

        // let mut rulep: usize = lr0.derives.derives[symbol1] as usize;
        // while lr0.derives.derives_rules[rulep] >= 0 {
        for &rule in lr0.derives.values(symbol1) {
            assert!(states.len() == 0);
            states.push(state1 as i16);
            let mut stateno: usize = state1;
            let mut rp: usize = gram.rrhs[rule as usize] as usize;
            while gram.ritem[rp] >= 0 {
                let symbol2 = gram.ritem[rp];
                for &shift in lr0.shifts.values(stateno) {
                    stateno = shift as usize;
                    if lr0.states[stateno].accessing_symbol == symbol2 {
                        break;
                    }
                }

                states.push(stateno as i16);
                rp += 1;
            }

            add_lookback_edge(stateno as State, rule, i, &lr0.reductions, &mut lookback);

            let mut length = states.len() - 1;
            let mut done_flag = false;
            while !done_flag {
                done_flag = true;
                rp -= 1;
                if gram.ritem[rp] >= 0 && gram.is_var(gram.ritem[rp]) {
                    length -= 1;
                    stateno = states[length] as usize;
                    edge.push(map_goto(gram, gotos, stateno, gram.ritem[rp]) as i16);
                    if nullable[gram.ritem[rp] as usize] && length > 0 {
                        done_flag = false;
                    }
                }
            }
            states.clear(); // prepare for next use
        }

        if edge.len() != 0 {
            let mut shortp: Vec<i16> = Vec::with_capacity(edge.len() + 1);
            shortp.extend(&edge);
            shortp.push(-1);
            includes[i] = shortp;
        }
        edge.clear(); // prepare for next use
    }

    (transpose(&includes), lookback)
}

// Adds an entry to the 'lookback' table.
fn add_lookback_edge(
    stateno: State,
    ruleno: Rule,
    gotono: usize,
    reductions: &Reductions,
    lookback: &mut Vec<Vec<i16>>,
) {
    let range = reductions.values_range(stateno as usize);
    let state_rules = reductions.values(stateno as usize);
    for (i, &r) in range.clone().zip(state_rules) {
        if r == ruleno {
            lookback[i].insert(0, gotono as i16);
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

    // if let Some(ref mut rp) = ds.R[i] {
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
