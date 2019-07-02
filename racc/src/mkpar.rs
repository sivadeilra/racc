use crate::Symbol;
use crate::grammar::Grammar;
use crate::lalr::LALROutput;
use crate::lr0::LR0Output;
use crate::lr0::Reductions;
use crate::State;
use log::debug;
use log::warn;

#[derive(Clone, Copy, PartialEq)]
pub enum ActionCode {
    Shift,
    Reduce,
}

pub const LEFT: u8 = 1;
pub const RIGHT: u8 = 2;

pub struct ParserAction {
    pub symbol: i16,
    pub number: i16,
    pub prec: i16,
    pub action_code: ActionCode,
    pub assoc: u8,
    pub suppressed: u8,
}

pub struct YaccParser {
    pub actions: Vec<Vec<ParserAction>>,
    pub default_reductions: Vec<i16>,
    pub final_state: State,
}
impl YaccParser {
    pub fn nstates(&self) -> usize {
        self.actions.len()
    }
}

pub fn make_parser(gram: &Grammar, lr0: &LR0Output, lalr: &LALROutput) -> YaccParser {
    let nstates = lr0.nstates();
    let mut parser: Vec<Vec<ParserAction>> = (0..nstates)
        .map(|state| parse_actions(gram, lr0, lalr, state as State))
        .collect();

    let final_state = find_final_state(gram, lr0);
    remove_conflicts(final_state, parser.as_mut_slice());
    report_unused_rules(gram, &parser);

    let defred = default_reductions(&parser);

    YaccParser {
        actions: parser,
        default_reductions: defred,
        final_state: final_state,
    }
}

fn parse_actions(
    gram: &Grammar,
    lr0: &LR0Output,
    lalr: &LALROutput,
    stateno: State,
) -> Vec<ParserAction> {
    let mut actions = get_shifts(gram, lr0, stateno);
    add_reductions(gram, &lr0.reductions, lalr, stateno, &mut actions);
    actions
}

fn get_shifts(gram: &Grammar, lr0: &LR0Output, stateno: State) -> Vec<ParserAction> {
    let mut actions: Vec<ParserAction> = Vec::new();
    for &k in lr0.shifts.values(stateno as usize) {
        let symbol = lr0.accessing_symbol[k as State];
        if gram.is_token(symbol) {
            actions.push(ParserAction {
                symbol: symbol.0,
                number: k,
                prec: gram.prec[symbol.0 as usize],
                action_code: ActionCode::Shift,
                assoc: gram.assoc[symbol.0 as usize],
                suppressed: 0,
            });
        }
    }
    actions
}

fn add_reductions(
    gram: &Grammar,
    reductions: &Reductions,
    lalr: &LALROutput,
    stateno: State,
    actions: &mut Vec<ParserAction>,
) {
    let range = reductions.values_range(stateno as usize);
    let state_rules = reductions.values(stateno as usize);
    for (i, &rule) in range.zip(state_rules) {
        for j in (0..gram.ntokens).rev() {
            if lalr.LA.get(i, j) {
                add_reduce(gram, actions, rule as usize, j as i16);
            }
        }
    }
}

fn add_reduce(gram: &Grammar, actions: &mut Vec<ParserAction>, ruleno: usize, symbol: i16) {
    let mut next: usize = 0;
    while next < actions.len() && actions[next].symbol < symbol {
        next += 1;
    }

    while next < actions.len()
        && actions[next].symbol == symbol
        && actions[next].action_code == ActionCode::Shift
    {
        next += 1;
    }

    while next < actions.len()
        && actions[next].symbol == symbol
        && actions[next].action_code == ActionCode::Reduce
        && (actions[next].number as usize) < ruleno
    {
        next += 1;
    }

    actions.insert(
        next,
        ParserAction {
            symbol: symbol,
            number: ruleno as i16,
            prec: gram.rprec[ruleno],
            action_code: ActionCode::Reduce,
            assoc: gram.rassoc[ruleno],
            suppressed: 0,
        },
    );
}

fn find_final_state(gram: &Grammar, lr0: &LR0Output) -> State {
    let goal = gram.ritem[1].as_symbol();
    let mut final_state: State = 0;
    for &ts in lr0.shifts.values(0).iter().rev() {
        final_state = ts;
        if lr0.accessing_symbol[final_state] == goal {
            return ts;
        }
    }
    // Is reaching here an error?
    final_state
}

fn report_unused_rules(gram: &Grammar, parser: &[Vec<ParserAction>]) {
    let mut rules_used = vec![false; gram.nrules];

    for pi in parser.iter() {
        for action in pi.iter() {
            if action.action_code == ActionCode::Reduce && action.suppressed == 0 {
                rules_used[action.number as usize] = true;
            }
        }
    }

    let num_unused = rules_used[3..].iter().filter(|&&used| !used).count();
    if num_unused != 0 {
        warn!("{} rule(s) were never reduced", num_unused);
    }
}

/// Modifies ParserAction::suppressed. That field could potentially be moved to a
/// separate vector, which this function would produce.
fn remove_conflicts(final_state: State, parser: &mut [Vec<ParserAction>]) {
    let mut srtotal = 0;
    let mut rrtotal = 0;
    for (i, pvec) in parser.iter_mut().enumerate() {
        let is_final_state = i as State == final_state;
        let (srcount, rrcount) = remove_conflicts_for_state(pvec, is_final_state);
        srtotal += srcount;
        rrtotal += rrcount;
    }
    if srtotal + rrtotal > 0 {
        total_conflicts(srtotal, rrtotal);
    }
}

/// Modifies ParserAction::suppressed. That field could potentially be moved to a
/// separate vector, which this function would produce.
/// Returns (shift_reduce_conflict_count, reduce_reduce_conflict_count)
fn remove_conflicts_for_state(pvec: &mut [ParserAction], is_final_state: bool) -> (usize, usize) {
    let mut srcount: usize = 0;
    let mut rrcount: usize = 0;
    if !pvec.is_empty() {
        let mut symbol: i16 = pvec[0].symbol;
        let mut pref: usize = 0; // index into pvec
        for p in 1..pvec.len() {
            // p is index into pvec
            if pvec[p].symbol != symbol {
                pref = p;
                symbol = pvec[p].symbol;
            } else if is_final_state && symbol == 0 {
                srcount += 1;
                pvec[p].suppressed = 1;
            } else if pvec[pref].action_code == ActionCode::Shift {
                if pvec[pref].prec > 0 && pvec[p].prec > 0 {
                    if pvec[pref].prec < pvec[p].prec {
                        pvec[pref].suppressed = 2;
                        pref = p;
                    } else if pvec[pref].prec > pvec[p].prec {
                        pvec[p].suppressed = 2;
                    } else if pvec[pref].assoc == LEFT {
                        pvec[pref].suppressed = 2;
                        pref = p;
                    } else if pvec[pref].assoc == RIGHT {
                        pvec[p].suppressed = 2;
                    } else {
                        pvec[pref].suppressed = 2;
                        pvec[p].suppressed = 2;
                    }
                } else {
                    srcount += 1;
                    pvec[p].suppressed = 1;
                }
            } else {
                rrcount += 1;
                pvec[p].suppressed = 1;
            }
        }
    }
    (srcount, rrcount)
}

fn total_conflicts(srtotal: usize, rrtotal: usize) {
    if srtotal > 0 {
        warn!("{} shift/reduce conflict(s)", srtotal);
    }

    if rrtotal > 1 {
        warn!("{} reduce/reduce conflict(s)", rrtotal);
    }
}

// Computese the default reduction for a single state.
fn sole_reduction(parser: &[ParserAction]) -> i16 {
    let mut count: usize = 0;
    let mut ruleno: i16 = 0;
    for p in parser.iter() {
        if p.action_code == ActionCode::Shift && p.suppressed == 0 {
            debug!("    found unsuppressed shift, returning 0");
            return 0;
        } else if p.action_code == ActionCode::Reduce && p.suppressed == 0 {
            if ruleno > 0 && p.number != ruleno {
                debug!(
                    "    found unsuppressed reduce for rule {}, returning 0",
                    ruleno
                );
                return 0;
            }
            debug!("    found unsuppressed reduce");
            if p.symbol != 1 {
                count += 1;
                debug!("    count --> {}", count);
            }
            ruleno = p.number;
            debug!("    selecting rule {}", ruleno);
        }
    }

    if count == 0 {
        debug!("    did not find any reductions");
        return 0;
    }
    debug!("    selected default reduction {}", ruleno);
    ruleno
}

/// Computes the default reduction for each state.
pub fn default_reductions(parser: &[Vec<ParserAction>]) -> Vec<i16> {
    debug!("default_reductions");
    parser
        .iter()
        .enumerate()
        .map(|(i, actions)| {
            let r = sole_reduction(actions);
            debug!("    state {} has default reduction {}", i, r);
            r
        })
        .collect()
}
