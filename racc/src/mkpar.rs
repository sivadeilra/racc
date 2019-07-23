use crate::grammar::Grammar;
use crate::lalr::LALROutput;
use crate::lr0::LR0Output;
use crate::lr0::Reductions;
use crate::ramp_table::RampTable;
use crate::{Rule, State, Token};
use log::debug;
use log::warn;

#[derive(Clone, Copy, PartialEq)]
pub enum ActionCode {
    Shift(State),
    Reduce(Rule),
}
impl ActionCode {
    pub fn is_shift(&self) -> bool {
        if let ActionCode::Shift(_) = self {
            true
        } else {
            false
        }
    }

    #[allow(dead_code)]
    pub fn is_reduce(&self) -> bool {
        if let ActionCode::Reduce(_) = self {
            true
        } else {
            false
        }
    }
}

pub const LEFT: u8 = 1;
pub const RIGHT: u8 = 2;

pub struct ParserAction {
    pub symbol: Token,
    pub prec: i16,
    pub action_code: ActionCode,
    pub assoc: u8,
    pub suppressed: u8,
}

pub struct YaccParser {
    /// State -> [ParserAction]
    pub actions: RampTable<ParserAction>,
    pub final_state: State,
}
impl YaccParser {
    pub fn nstates(&self) -> usize {
        self.actions.num_keys()
    }
}

pub fn make_parser(gram: &Grammar, lr0: &LR0Output, lalr: &LALROutput) -> YaccParser {
    let nstates = lr0.nstates();
    let mut parser: RampTable<ParserAction> = RampTable::new();
    for state in 0..nstates {
        let state: State = state.into();
        get_shifts(gram, lr0, state, &mut parser);
        get_reductions(gram, &lr0.reductions, lalr, state, &mut parser);
        parser.finish_key();
    }

    let final_state = find_final_state(gram, lr0);
    remove_conflicts(final_state, &mut parser);
    report_unused_rules(gram, &parser);

    YaccParser {
        actions: parser,
        final_state: final_state,
    }
}

fn get_shifts(
    gram: &Grammar,
    lr0: &LR0Output,
    stateno: State,
    actions: &mut RampTable<ParserAction>,
) {
    for &k in lr0.shifts.values(stateno) {
        let symbol = lr0.accessing_symbol[k];
        if gram.is_token(symbol) {
            actions.push_value(ParserAction {
                symbol: gram.symbol_to_token(symbol),
                prec: gram.prec[symbol.index()],
                action_code: ActionCode::Shift(k),
                assoc: gram.assoc[symbol.index()],
                suppressed: 0,
            });
        }
    }
}

fn get_reductions(
    gram: &Grammar,
    reductions: &Reductions,
    lalr: &LALROutput,
    stateno: State,
    actions: &mut RampTable<ParserAction>,
) {
    let range = reductions.values_range(stateno);
    let state_rules = reductions.values(stateno);
    for (i, &rule) in range.zip(state_rules) {
        for j in (0..gram.ntokens).rev() {
            if lalr.LA.get(i, j) {
                add_reduce(gram, actions, rule, Token(j as i16));
            }
        }
    }
}

/// Inserts a new value into the 'actions' table, in a sorted position.
/// This inserts one new value into the 'values' of the 'actions' table, at the end.
/// It is careful to insert items in a sorted order.
fn add_reduce(gram: &Grammar, actions: &mut RampTable<ParserAction>, rule: Rule, symbol: Token) {
    // end: index of the values of the current (unfinished) key
    let end = *actions.index.last().unwrap();
    let actions = &mut actions.table;
    let mut next: usize = end;
    while next < actions.len() && actions[next].symbol < symbol {
        next += 1;
    }

    while next < actions.len()
        && actions[next].symbol == symbol
        && actions[next].action_code.is_shift()
    {
        next += 1;
    }

    // find insertion position for a Reduce action
    while next < actions.len() && actions[next].symbol == symbol {
        let action = &actions[next];
        if let ActionCode::Reduce(action_rule) = action.action_code {
            if action_rule < rule {
                next += 1;
                continue;
            }
        }
        break;
    }

    actions.insert(
        next,
        ParserAction {
            symbol: symbol,
            prec: gram.rprec[rule.index()],
            action_code: ActionCode::Reduce(rule),
            assoc: gram.rassoc[rule.index()],
            suppressed: 0,
        },
    );
}

fn find_final_state(gram: &Grammar, lr0: &LR0Output) -> State {
    let goal = gram.ritem[1].as_symbol();
    let mut final_state: State = State(0);
    for &ts in lr0.shifts.values(0usize).iter().rev() {
        final_state = ts;
        if lr0.accessing_symbol[final_state] == goal {
            return ts;
        }
    }
    // Is reaching here an error?
    final_state
}

fn report_unused_rules(gram: &Grammar, parser: &RampTable<ParserAction>) {
    let mut rules_used = vec![false; gram.nrules];
    for state_actions in parser.iter_entries() {
        for action in state_actions.iter() {
            if let ActionCode::Reduce(action_rule) = action.action_code {
                if action.suppressed == 0 {
                    rules_used[action_rule.index()] = true;
                }
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
fn remove_conflicts(final_state: State, parser: &mut RampTable<ParserAction>) {
    let mut srtotal = 0;
    let mut rrtotal = 0;
    for (state, actions) in parser.iter_entries_mut().enumerate() {
        let state = State(state as i16);
        let is_final_state = state == final_state;
        let (srcount, rrcount) = remove_conflicts_for_state(actions, is_final_state);
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
fn remove_conflicts_for_state(
    actions: &mut [ParserAction],
    is_final_state: bool,
) -> (usize, usize) {
    let mut srcount: usize = 0;
    let mut rrcount: usize = 0;
    let mut iter_actions = actions.iter_mut();
    if let Some(first) = iter_actions.next() {
        // preferred
        let mut pref = first;
        let mut symbol = pref.symbol;
        for p in iter_actions {
            if p.symbol != symbol {
                pref = p;
                symbol = pref.symbol;
            } else if is_final_state && symbol == Token(0) {
                srcount += 1;
                p.suppressed = 1;
            } else if let ActionCode::Shift(_) = pref.action_code {
                if pref.prec > 0 && p.prec > 0 {
                    if pref.prec < p.prec {
                        pref.suppressed = 2;
                        pref = p;
                    } else if pref.prec > p.prec {
                        p.suppressed = 2;
                    } else if pref.assoc == LEFT {
                        pref.suppressed = 2;
                        pref = p;
                    } else if pref.assoc == RIGHT {
                        p.suppressed = 2;
                    } else {
                        pref.suppressed = 2;
                        p.suppressed = 2;
                    }
                } else {
                    srcount += 1;
                    p.suppressed = 1;
                }
            } else {
                rrcount += 1;
                p.suppressed = 1;
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
fn sole_reduction(parser: &[ParserAction]) -> Rule {
    let mut count: usize = 0;
    let mut ruleno = Rule(0);
    for p in parser.iter() {
        match &p.action_code {
            ActionCode::Shift(_) => {
                if p.suppressed == 0 {
                    debug!("    found unsuppressed shift, returning 0");
                    return Rule(0);
                }
            }
            ActionCode::Reduce(reduce_rule) => {
                if p.suppressed == 0 {
                    if ruleno > Rule(0) && *reduce_rule != ruleno {
                        debug!(
                            "    found unsuppressed reduce for rule {}, returning 0",
                            ruleno
                        );
                        return Rule(0);
                    }
                    debug!("    found unsuppressed reduce");
                    if p.symbol != Token(1) {
                        count += 1;
                        debug!("    count --> {}", count);
                    }
                    ruleno = *reduce_rule;
                    debug!("    selecting rule {}", ruleno);
                }
            }
        }
    }

    if count == 0 {
        debug!("    did not find any reductions");
        return Rule(0);
    }
    debug!("    selected default reduction {}", ruleno);
    ruleno
}

/// Computes the default reduction for each state.
/// State -> Rule
pub fn default_reductions(parser: &RampTable<ParserAction>) -> Vec<Rule> {
    parser
        .iter_entries()
        .map(|actions| sole_reduction(actions))
        .collect()
}
