use std::collections::Bitv;
use std::iter::repeat;

use grammar::Grammar;
use lr0::LR0Output;
use lalr::LALROutput;
use util::{reverse_range};

#[derive(Copy,PartialEq)]
pub enum ActionCode {
    Shift = 1,
    Reduce = 2,
}

pub const LEFT: u8 = 1;
pub const RIGHT: u8 = 2;

pub struct ParserAction {
    pub symbol: i16,
    pub number: i16,
    pub prec: i16,
    pub action_code: ActionCode,
    pub assoc: u8,
    pub suppressed: u8
}

pub struct YaccParser {
    pub nstates: uint,
    pub actions: Vec<Vec<ParserAction>>,
    pub default_reductions: Vec<i16>,
    pub final_state: uint
}

pub fn make_parser(gram: &Grammar, lr0: &LR0Output, lalr: &LALROutput) -> YaccParser {
    let mut parser: Vec<Vec<ParserAction>> = Vec::with_capacity(lr0.nstates());
    for state in range(0, lr0.nstates()) {
        parser.push(parse_actions(gram, lr0, lalr, state));
    }

    let final_state = find_final_state(gram, lr0, lalr);
    remove_conflicts(lr0, final_state, &mut parser);
    unused_rules(gram, &parser);
    let defred = default_reductions(lr0, &parser);

    YaccParser {
        nstates: lr0.nstates(),
        actions: parser,
        default_reductions: defred,
        final_state: final_state
    }
}

fn parse_actions(gram: &Grammar, lr0: &LR0Output, lalr: &LALROutput, stateno: uint) -> Vec<ParserAction> {
    let mut actions = get_shifts(gram, lr0, lalr, stateno);
    add_reductions(gram, lalr, stateno, &mut actions);
    actions
}

fn get_shifts(gram: &Grammar, lr0: &LR0Output, lalr: &LALROutput, stateno: uint) -> Vec<ParserAction> {
    let mut actions: Vec<ParserAction> = Vec::new();
    if lalr.shift_table[stateno] != -1 {
        let sp = &lr0.shifts[lalr.shift_table[stateno] as uint];
        let to_state2 = &sp.shifts;
        for i in reverse_range(sp.shifts.len(), 0) {
            let k = to_state2[i] as uint;
            let symbol = lr0.states[k].accessing_symbol;
            if gram.is_token(symbol) {
                actions.push(ParserAction {
                    symbol: symbol as i16,
                    number: k as i16,
                    prec: gram.prec[symbol],
                    action_code: ActionCode::Shift,
                    assoc: gram.assoc[symbol],
                    suppressed: 0
                });
            }
        }
    }

    // For compatibility with C implementation, which used a singly-linked list
    actions.reverse();
    actions
}

fn add_reductions(gram: &Grammar, lalr: &LALROutput, stateno: uint, actions: &mut Vec<ParserAction>) {
    let m = lalr.lookaheads[stateno] as uint;
    let n = lalr.lookaheads[stateno + 1] as uint;
    for i in range(m, n) {
        let ruleno = lalr.laruleno[i] as uint;
        for j in reverse_range(gram.ntokens, 0) {
            if lalr.LA.get(i, j) {
                add_reduce(gram, actions, ruleno, j);
            }
        }
    }
}

fn add_reduce(gram: &Grammar, actions: &mut Vec<ParserAction>, ruleno: uint, symbol: uint) {
    let symbol16 = symbol as i16;
    let mut next: uint = 0;
    while next < actions.len() && actions[next].symbol < symbol16 {
        next += 1;
    }

    while next < actions.len() && actions[next].symbol == symbol16 && actions[next].action_code == ActionCode::Shift {
        next += 1;
    }

    while next < actions.len() && actions[next].symbol == symbol16 && actions[next].action_code == ActionCode::Reduce && (actions[next].number as uint) < ruleno {
        next += 1;
    }

    let temp = ParserAction {
        symbol: symbol16,
        number: ruleno as i16,
        prec: gram.rprec[ruleno],
        action_code: ActionCode::Reduce,
        assoc: gram.rassoc[ruleno],
        suppressed: 0
    };

    actions.insert(next, temp);
}

fn find_final_state(gram: &Grammar, lr0: &LR0Output, lalr: &LALROutput) -> uint
{
    let p = &lr0.shifts[lalr.shift_table[0] as uint];
    let to_state2 = &p.shifts;
    let goal = gram.ritem[1] as uint;
    let mut final_state: uint = 0;
    for i in reverse_range(to_state2.len(), 0) {
        final_state = to_state2[i] as uint;
        if lr0.states[final_state].accessing_symbol == goal {
            break;
        }
    }
    final_state
}

fn unused_rules(gram: &Grammar, parser: &Vec<Vec<ParserAction>>)
{
    let mut rules_used: Bitv = Bitv::from_elem(gram.nrules, false);

    for pi in parser.iter() {
        for p in pi.iter() {
            if p.action_code == ActionCode::Reduce && p.suppressed == 0 {
                rules_used.set(p.number as uint, true);
            }
        }
    }

    let mut nunused: uint = 0;
    for i in range(3, gram.nrules) {
        if !rules_used[i] {
            nunused += 1;
        }
    }

    if nunused != 0 {
        warn!("{} rule(s) were never reduced", nunused);
    }
}

fn remove_conflicts(lr0: &LR0Output, final_state: uint, parser: &mut Vec<Vec<ParserAction>>) {
    let mut srtotal = 0;
    let mut rrtotal = 0;
    let mut srconflicts: Vec<i16> = repeat(0).take(lr0.nstates()).collect();
    let mut rrconflicts: Vec<i16> = repeat(0).take(lr0.nstates()).collect();
    for i in range(0, lr0.nstates()) {
        let pvec = &mut parser[i];
        let mut srcount: uint = 0;
        let mut rrcount: uint = 0;
        if pvec.len() > 0 {
            let mut symbol: i16 = pvec[0].symbol;
            let mut pref: uint = 0; // index into pvec
            for p in range(1, pvec.len()) { // p is index into pvec
                if pvec[p].symbol != symbol {
                    pref = p;
                    symbol = pvec[p].symbol;
                }
                else if i == final_state && symbol == 0 {
                    srcount += 1;
                    pvec[p].suppressed = 1;
                }
                else if pvec[pref].action_code == ActionCode::Shift {
                    if pvec[pref].prec > 0 && pvec[p].prec > 0 {
                        if pvec[pref].prec < pvec[p].prec {
                            pvec[pref].suppressed = 2;
                            pref = p;
                        }
                        else if pvec[pref].prec > pvec[p].prec {
                            pvec[p].suppressed = 2;
                        }
                        else if pvec[pref].assoc == LEFT {
                            pvec[pref].suppressed = 2;
                            pref = p;
                        }
                        else if pvec[pref].assoc == RIGHT {
                            pvec[p].suppressed = 2;
                        }
                        else {
                            pvec[pref].suppressed = 2;
                            pvec[p].suppressed = 2;
                        }
                    }
                    else {
                        srcount += 1;
                        pvec[p].suppressed = 1;
                    }
                }
                else {
                    rrcount += 1;
                    pvec[p].suppressed = 1;
                }
            }        
        }

        srtotal += srcount;
        rrtotal += rrcount;
        srconflicts[i] = srcount as i16;
        rrconflicts[i] = rrcount as i16;
    }

    if srtotal + rrtotal > 0 {
        total_conflicts(srtotal, rrtotal);
    }
}

fn total_conflicts(srtotal: uint, rrtotal: uint)
{
    if srtotal > 0 {
        warn!("{} shift/reduce conflict(s)", srtotal);
    }

    if rrtotal > 1 {
        warn!("{} reduce/reduce conflict(s)", rrtotal);
    }
}

fn sole_reduction(stateno: uint, parser: &Vec<Vec<ParserAction>>) -> uint {
    debug!("sole_reduction: state={}", stateno);
    let mut count: uint = 0;
    let mut ruleno: uint = 0;
    for p in parser[stateno].iter() {
        if p.action_code == ActionCode::Shift && p.suppressed == 0 {
            debug!("    found unsuppressed shift, returning 0");
            return 0;
        }
        else if p.action_code == ActionCode::Reduce && p.suppressed == 0 {
            if ruleno > 0 && (p.number as uint) != ruleno {
                debug!("    found unsuppressed reduce for rule {}, returning 0", ruleno);
                return 0;
            }
            debug!("    found unsuppressed reduce");
            if p.symbol != 1 {
                count += 1;
                debug!("    count --> {}", count);
            }
            ruleno = p.number as uint;
            debug!("    selecting rule {}", ruleno);
        }
    }

    if count == 0 {
        debug!("    did not find any reductions");
        return 0;
    }
    debug!("    selected default reduction {}", ruleno);
    return ruleno;
}

fn default_reductions(lr0: &LR0Output, parser: &Vec<Vec<ParserAction>>) -> Vec<i16>
{
    debug!("default_reductions");
    let mut defred: Vec<i16> = Vec::with_capacity(lr0.nstates());
    for i in range(0, lr0.nstates()) {
        let r = sole_reduction(i, parser);
        debug!("    state {} has default reduction {}", i, r);
        defred.push(r as i16);
    }
    defred
}
