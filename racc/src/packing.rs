use super::*;

/// The function matching_vector determines if the vector specified by
/// the input parameter matches a previously considered vector. The
/// test at the start of the function checks if the vector represents
/// a row of shifts over terminal symbols or a row of reductions, or a
/// column of shifts over a nonterminal symbol.  Berkeley Yacc does not
/// check if a column of shifts over a nonterminal symbols matches a
/// previously considered vector.  Because of the nature of LR parsing
/// tables, no two columns can match.  Therefore, the only possible
/// match would be between a row and a column.  Such matches are
/// unlikely.  Therefore, to save time, no attempt is made to see if a
/// column matches a previously considered vector.
///
/// Matching_vector is poorly designed.  The test could easily be made
/// faster.  Also, it depends on the vectors being in a specific
/// order.
fn matching_vector(pack: &PackState<'_>, vector: usize) -> Option<usize> {
    let i = pack.order[vector];
    if i >= 2 * pack.nstates {
        // Never match among variable gotos.
        return None;
    }

    let act = pack.act;
    let t = act.tally(i);
    let w = act.width(i);
    for &j in pack.order[0..vector].iter().rev() {
        if act.width(j) != w || act.tally(j) != t {
            return None;
        }
        if act.tos[i] == act.tos[j] && act.froms[i] == act.froms[j] {
            return Some(j);
        }
    }
    None
}

fn pack_vector(pack: &mut PackState<'_>, vector: usize) -> i16 {
    // log::debug!("pack_vector: vector={} lowzero={}", vector, pack.lowzero);
    let act = pack.act;
    let i = pack.order[vector];
    let from = &act.froms[i];
    let to = &act.tos[i];
    let t = from.len();
    assert!(t != 0);

    let mut j: i16 = pack.lowzero - from[0];
    for &f in from[1..t].iter() {
        if pack.lowzero - f > j {
            j = pack.lowzero - f;
        }
    }

    loop {
        if j == 0 {
            j = 1;
            continue;
        }

        let mut ok = true;
        for &f in &from[0..t] {
            let loc = (j + f) as usize;

            // make sure we can read/write table[loc] and table[check]
            if loc >= pack.table.len() {
                assert!(pack.table.len() == pack.check.len());
                pack.table.resize(loc + 1, 0);
                pack.check.resize(loc + 1, -1);
            }

            if pack.check[loc] != -1 {
                ok = false;
                break;
            }
        }
        if !ok {
            j += 1;
            continue;
        }
        if pack.pos[0..vector].iter().any(|&p| p == j) {
            j += 1;
            continue;
        }

        for (&f, &t) in from[0..t].iter().zip(to[0..t].iter()) {
            let loc = (j + f) as usize;
            pack.table[loc] = t;
            pack.check[loc] = f;
            if loc > pack.high {
                pack.high = loc;
            }
        }

        while pack.check[pack.lowzero as usize] != -1 {
            pack.lowzero += 1;
        }

        return j;
    }
}

struct PackState<'a> {
    base: Vec<i16>,
    pos: Vec<i16>,
    table: Vec<i16>, // table and check always have same len
    check: Vec<i16>, // table is 0-filled, check is -1-filled
    lowzero: i16,
    high: usize,

    order: &'a [usize],
    nstates: usize,
    act: &'a ActionsTable,
}

pub(crate) struct PackedTables {
    pub base: Vec<i16>,
    pub table: Vec<i16>,
    pub check: Vec<i16>,
    pub nstates: usize,
}

impl PackedTables {
    pub(crate) fn rindex_table(&self) -> &[i16] {
        &self.base[self.nstates..self.nstates * 2]
    }

    pub(crate) fn sindex_table(&self) -> &[i16] {
        &self.base[..self.nstates]
    }

    pub(crate) fn gindex_table(&self) -> &[i16] {
        &self.base[self.nstates * 2..self.base.len() - 1]
    }
}

pub(crate) fn pack_table(nstates: usize, order: &[usize], act: &ActionsTable) -> PackedTables {
    debug!("pack_table: nentries={}", order.len());

    let initial_maxtable = 1000;

    let mut pack = PackState {
        base: vec![0; act.nvectors],
        pos: vec![0; order.len()],
        table: vec![0; initial_maxtable],
        check: vec![-1; initial_maxtable],
        lowzero: 0,
        high: 0,
        order,
        nstates,
        act,
    };

    for (i, o) in order.iter().enumerate() {
        let place = match matching_vector(&pack, i) {
            Some(state) => pack.base[state],
            None => pack_vector(&mut pack, i),
        };

        pack.pos[i] = place;
        pack.base[*o] = place;
    }

    pack.check.truncate(pack.high + 1);
    pack.table.truncate(pack.high + 1);

    PackedTables {
        base: pack.base,
        table: pack.table,
        check: pack.check,
        nstates,
    }
}
