use grammar::Grammar;
use util::Bitmat;
use lr0::LR0Output;
use std::iter::repeat;

#[allow(non_snake_case)]
pub struct LALROutput {
    pub shift_table: Vec<i16>,
    pub reduction_table: Vec<i16>,
    pub lookaheads: Vec<i16>,
    pub laruleno: Vec<i16>,
    pub LA: Bitmat,
    pub gotos: GotoMap
}

pub struct GotoMap {
    pub ngotos: usize,
    pub goto_map: Vec<i16>,
    pub from_state: Vec<i16>,
    pub to_state: Vec<i16>
}

#[allow(non_snake_case)]
pub fn run_lalr(gram: &Grammar, lr0: &LR0Output) -> LALROutput
{
    let shift_table = set_shift_table(lr0);
    let reduction_table = set_reduction_table(lr0);
    let lookaheads = create_lookaheads(lr0, reduction_table.as_slice());

    // the LA and lookback tables have len() = LA_len
    let LA_len = lookaheads[lookaheads.len() - 1] as usize;

    let laruleno = initialize_LA(lr0, LA_len, reduction_table.as_slice());
    let gotos = set_goto_map(gram, lr0);

    let mut F = initialize_F(gram, lr0, &gotos, shift_table.as_slice());

    let (includes, lookback) = build_relations(gram, lr0, shift_table.as_slice(), &gotos, lookaheads.as_slice(), laruleno.as_slice(), LA_len);
    
    compute_FOLLOWS(&includes, &mut F);
    
    let LA = compute_lookaheads(gram, lr0, lookaheads.as_slice(), &lookback, &F);

    LALROutput {
        shift_table: shift_table,
        reduction_table: reduction_table,
        laruleno: laruleno,
        lookaheads: lookaheads,
        LA: LA,
        gotos: gotos
    }
}

fn set_shift_table(lr0: &LR0Output) -> Vec<i16>
{
    let mut shift_table: Vec<i16> = repeat(-1).take(lr0.states.len()).collect();
    for i in 0..lr0.shifts.len() {
        let state = lr0.shifts[i].state;
        assert!(shift_table[state] == -1);
        shift_table[state] = i as i16;
    }
    shift_table
}

// Builds a table which maps from states to reductions.
// The index of each element corresponds to a state index.
// The value of each element is either -1, for states that
// do not have any reductions, or an index into LR0Output.reductions.
fn set_reduction_table(lr0: &LR0Output) -> Vec<i16> {
    let mut reduction_table: Vec<i16> = repeat(-1).take(lr0.states.len()).collect();
    for i in 0..lr0.reductions.len() {
        let state = lr0.reductions[i].state;
        assert!(reduction_table[state] == -1);
        reduction_table[state] = i as i16;
    }
    reduction_table
}

// Finds the longest rhs
fn set_max_rhs(gram: &Grammar) -> usize {
    let mut length: usize = 0;
    let mut max: usize = 0;
    for itemp in 0..gram.nitems {
        if gram.ritem[itemp] >= 0 {
            length += 1;
        }
        else {
            if length > max {
                max = length;
            }
            length = 0;
        }
    }
    max
}

// Creates the 'lookaheads' table.  (This is not the same as the LA table.)
// The index of each entry in 'lookaheads' corresponds to a state, plus one
// extra entry at the end which corresponds to nstates.  The value of each
// entry is the sum of rules for all reductions in the previous states.
fn create_lookaheads(lr0: &LR0Output, reduction_table: &[i16]) -> Vec<i16> {
    let mut lookaheads: Vec<i16> = Vec::with_capacity(lr0.states.len() + 1);

    // Count the total number of reductions, and also build the lookaheads table.
    let mut k = 0;
    for i in 0..lr0.states.len() {
        lookaheads.push(k as i16);
        let rp = reduction_table[i];
        if rp != -1 {
            k += lr0.reductions[rp as usize].rules.len();
        }
    }
    lookaheads.push(k as i16);
    assert!(lookaheads.len() == lr0.states.len() + 1);
    lookaheads    
}

#[allow(non_snake_case)]
fn initialize_LA(lr0: &LR0Output, LA_len: usize, reduction_table: &[i16]) -> Vec<i16> {
    let mut laruleno: Vec<i16> = repeat(0).take(LA_len).collect();
    let mut k: usize = 0;
    for i in 0..lr0.states.len() {
        let rp = reduction_table[i];
        if rp != -1 {
            let r = &lr0.reductions[rp as usize];
            for j in 0..r.rules.len() {
                laruleno[k] = r.rules[j];
                k += 1;
            }
        }
    }
    assert!(k == LA_len);
    laruleno
}

fn set_goto_map(gram: &Grammar, lr0: &LR0Output) -> GotoMap {
    // Count the number of gotos for each variable.
    let mut goto_map: Vec<i16> = repeat(0).take(gram.nvars + 1).collect();
    let mut ngotos: usize = 0;
    for sp in lr0.shifts.iter() {
        for i in (0..sp.shifts.len()).rev() {
            let state = sp.shifts[i] as usize;
            let symbol = lr0.states[state].accessing_symbol;

            if gram.is_token(symbol) {
                break;
            }

            assert!(ngotos < 0x7fff);
            ngotos += 1;
            goto_map[symbol - gram.ntokens] += 1;
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

    let mut from_state: Vec<i16> = repeat(0).take(ngotos).collect();
    let mut to_state: Vec<i16> = repeat(0).take(ngotos).collect();

    for sp in lr0.shifts.iter() {
        for i in (0..sp.shifts.len()).rev() {
            let state2 = sp.shifts[i];
            let symbol = lr0.states[state2 as usize].accessing_symbol;
            if gram.is_token(symbol as usize) {
                break;
            }

            let k = temp_map[symbol - gram.ntokens] as usize;
            temp_map[symbol - gram.ntokens] += 1;
            from_state[k] = sp.state as i16;
            to_state[k] = state2;
        }
    }

    debug!("set_goto_map: ngotos={}", ngotos);
    for i in 0..ngotos {
        debug!("    from {:3} to {:3}", from_state[i], to_state[i]);
    }

    debug!("goto_map:");
    for i in 0..gram.nvars {
        debug!("    {:3} {} --> {}", i, gram.name[i + gram.ntokens], goto_map[i]);
    }
    debug!(".");

    GotoMap { ngotos: ngotos, goto_map: goto_map, from_state: from_state, to_state: to_state }
}

// returns an index into goto_map
fn map_goto(
    gram: &Grammar,
    gotos: &GotoMap,
    state: usize, 
    symbol: usize) -> usize
{
    let var = symbol - gram.ntokens;
    let init_low =gotos.goto_map[var] as usize;
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
        }
        else {
            high = middle - 1;
        }
    }
}

#[allow(non_snake_case)]
fn initialize_F(
    gram: &Grammar, 
    lr0: &LR0Output,
    gotos: &GotoMap,
    shift_table: &[i16]) -> Bitmat
{
    debug!("initialize_F");

    let ngotos = gotos.ngotos;
    let mut F = Bitmat::new(ngotos, gram.ntokens);
    let mut reads: Vec<Vec<i16>> = repeat(Vec::new()).take(ngotos).collect();
    let mut edge: Vec<i16> = Vec::with_capacity(ngotos + 1);

    for i in 0..ngotos {
        let stateno = gotos.to_state[i] as usize;
        let sp = shift_table[stateno];

        if sp != -1 {
            let sp = &lr0.shifts[sp as usize];
            let k = sp.shifts.len();

            let mut j: usize = 0;
            while j < k {
                let symbol = lr0.states[sp.shifts[j] as usize].accessing_symbol;
                if gram.is_var(symbol) {
                    break;
                }
                F.set(i, symbol);
                j += 1;
            }

            while j < k {
                let symbol = lr0.states[sp.shifts[j] as usize].accessing_symbol;
                if lr0.nullable[symbol] {
                    let e = map_goto(gram, gotos, stateno, symbol);
                    edge.push(e as i16);
                }
                j += 1;
            }

            if edge.len() != 0 {
                let mut rp: Vec<i16> = Vec::with_capacity(edge.len() + 1);
                rp.reserve_exact(edge.len() + 1);
                rp.push_all(edge.as_slice());
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

#[allow(non_snake_case)]
fn build_relations(
    gram: &Grammar,
    lr0: &LR0Output,
    shift_table: &[i16],
    gotos: &GotoMap,
    lookaheads: &[i16],
    laruleno: &[i16],
    LA_len: usize) -> (Vec<Vec<i16>>, /*lookback:*/ Vec<Vec<i16>>)
{
    debug!("build_relations");

    let ngotos = gotos.ngotos;
    let mut includes: Vec<Vec<i16>> =  repeat(Vec::new()).take(ngotos).collect();
    let mut edge: Vec<i16> = Vec::with_capacity(ngotos + 1);                // temporary, reused in loops
    let mut states: Vec<i16> = Vec::with_capacity(set_max_rhs(gram) + 1);   // temporary, reused in loops
    let mut lookback: Vec<Vec<i16>> = repeat(Vec::new()).take(LA_len).collect();

    for i in 0..ngotos {
        assert!(edge.len() == 0);
        assert!(states.len() == 0);

        let state1 = gotos.from_state[i] as usize;
        let symbol1 = lr0.states[gotos.to_state[i] as usize].accessing_symbol;

        let mut rulep: usize = lr0.derives[symbol1] as usize;
        while lr0.derives_rules[rulep] >= 0 {
            assert!(states.len() == 0);
            states.push(state1 as i16);
            let mut stateno: usize = state1;
            let mut rp: usize = gram.rrhs[lr0.derives_rules[rulep] as usize] as usize;
            while gram.ritem[rp] >= 0 {
                let symbol2 = gram.ritem[rp] as usize;
                for shift in lr0.shifts[shift_table[stateno] as usize].shifts.iter() {
                    stateno = *shift as usize;
                    if lr0.states[stateno].accessing_symbol == symbol2 {
                        break;
                    }
                }

                states.push(stateno as i16);
                rp += 1;
            }

            add_lookback_edge(stateno, lr0.derives_rules[rulep] as usize, i, laruleno, lookaheads, &mut lookback);

            let mut length = states.len() - 1;
            let mut done_flag = false;
            while !done_flag {
                done_flag = true;
                rp -= 1;
                if gram.ritem[rp] >= 0 && gram.is_var(gram.ritem[rp] as usize) {
                    length -= 1;
                    stateno = states[length] as usize;
                    edge.push(map_goto(gram, gotos, stateno, gram.ritem[rp] as usize) as i16);
                    if lr0.nullable[gram.ritem[rp] as usize] && length > 0 {
                        done_flag = false;
                    }
                }
            }
            states.clear(); // prepare for next use
            rulep += 1;
        }

        if edge.len() != 0 {
            let mut shortp: Vec<i16> = Vec::with_capacity(edge.len() + 1);
            shortp.push_all(edge.as_slice());
            shortp.push(-1);
            includes[i] = shortp;
        }
        edge.clear(); // prepare for next use
    }

    (transpose(&includes, ngotos), lookback)
}

// Adds an entry to the 'lookback' table.
fn add_lookback_edge(stateno: usize, ruleno: usize, gotono: usize, laruleno: &[i16], lookaheads: &[i16], lookback: &mut Vec<Vec<i16>>)
{
    let mut i = lookaheads[stateno] as usize;
    let k = lookaheads[stateno + 1] as usize;
    loop {
        assert!(i < k);
        if (laruleno[i] as usize) == ruleno {
            lookback[i].insert(0, gotono as i16);
            break;
        }
        else {
            i += 1;
        }
    }
}

#[allow(non_snake_case)]
fn transpose(r2: &Vec<Vec<i16>>, n: usize) -> Vec<Vec<i16>>
{
    assert!(r2.len() == n);

    let mut nedges: Vec<i16> = repeat(0).take(n).collect();
    for i in 0..n {
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

    let mut new_R: Vec<Vec<i16>> = repeat(Vec::new()).take(n).collect();

    for i in 0..n {
        let k = nedges[i];
        if k > 0 {
            let mut sp: Vec<i16> = repeat(0).take((k as usize) + 1).collect();
            sp[k as usize] = -1;
            new_R[i] = sp;
        }
    }
    drop(nedges);

    let mut temp_R: Vec<i16> = repeat(0).take(n).collect();        // contains output columns
    for i in 0..n {              // i is old-row
        let sp = &r2[i];
        let mut j: usize = 0;            // j is old-col
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

    return new_R;
}

#[allow(non_snake_case)]
fn compute_FOLLOWS(includes: &Vec<Vec<i16>>, F: &mut Bitmat) {
    digraph(includes, F);
}

#[allow(non_snake_case)]
fn compute_lookaheads(gram: &Grammar, lr0: &LR0Output, lookaheads: &[i16], lookback: &Vec<Vec<i16>>, F: &Bitmat) -> Bitmat {
    let n = lookaheads[lr0.nstates()] as usize;
    let mut LA = Bitmat::new(n, gram.ntokens);

    assert!(F.cols == LA.cols);
    assert!(F.rowsize == LA.rowsize);

    for i in 0..n {
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
    R: &'a Vec<Vec<i16>>,
    F: &'a mut Bitmat
}

#[allow(non_snake_case)]
fn digraph(relation: &Vec<Vec<i16>>, F: &mut Bitmat) {
    let ngotos = F.rows;
    let mut ds = DigraphState {
        infinity: ngotos + 2,
        index: repeat(0).take(ngotos + 1).collect(),
        vertices: repeat(0).take(ngotos + 1).collect(),
        top: 0,
        R: relation,
        F: F
    };

    for i in 0..ngotos {
        if ds.index[i] == 0 && relation[i].len() != 0 {
            traverse(&mut ds, i);
        }
    }
}

fn traverse(ds: &mut DigraphState, i: usize) {
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
