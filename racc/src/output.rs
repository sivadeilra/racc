use crate::grammar::Grammar;
use crate::lalr::GotoMap;
use crate::mkpar::{ActionCode, YaccParser};
use crate::{Rule, State, StateOrRule, Symbol};
use log::debug;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use std::cmp;
use std::i16;
use std::iter::repeat;
use syn::{Block, Ident, Type};

// Given a constructed parser (a description of a state machine which parses
// a given grammar), produces a Rust AST which implements the parser.
pub fn output_parser_to_ast(
    gram: &Grammar,
    gotos: &GotoMap,
    parser: &YaccParser,
    blocks: &[Option<Block>],
    rhs_bindings: &[Option<Ident>],
    context_ty: Type, // Ident to use for the context type, passed to the reduce() method
    context_param_ident: Ident, // Ident to use for the context arg, passed to the reduce() method
    symbol_value_ty: Type, // type to use for value_stack
) -> TokenStream {
    assert!(blocks.len() == gram.nrules);

    let grammar_span = Span::call_site();
    let sp = grammar_span;

    let mut items: TokenStream = TokenStream::new();

    //  Generate YYDEFRED table.
    let yydefred: Vec<i16> = parser
        .default_reductions
        .iter()
        .map(|&s| if s != Rule(0) { s.0 - 2 } else { 0 })
        .collect();
    items.extend({ make_table_i16(Ident::new("YYDEFRED", sp), &yydefred) });

    items.extend(output_actions(grammar_span, gram, gotos, parser));
    // println!("output_actions done");

    for t in 1..gram.ntokens {
        // todo: use the original Ident from parsing, for better error reporting
        let tokvalue = gram.value[t] as u32;
        let tok_ident = &gram.name[t];
        items.extend(quote!(const #tok_ident: u32 = #tokvalue;));
    }
    // println!("tokens consts done");

    // Generate YYFINAL constant.
    let yyfinal = parser.final_state.0 as usize;
    items.extend(quote! {
        const YYFINAL: usize = #yyfinal;
    });

    // Build up actions
    let mut action_arms: TokenStream = TokenStream::new();
    for (rule_i, block) in blocks.iter().enumerate() {
        if rule_i < 3 {
            continue;
        }
        let rule = Rule(rule_i as i16);

        // Based on the rule we are reducing, get values from the value stack,
        // and bind them as a tuple named 'args'.

        let stmts: TokenStream = match block {
            Some(block) => {
                // We need to pop items off the stack and associate them with variables from right to left.
                let rhs_index = gram.rrhs(rule).0 as usize;
                let num_rhs = gram.get_rhs_items(rule).len();
                let mut t = TokenStream::new();
                for rhs_binding in rhs_bindings[rhs_index..rhs_index + num_rhs].iter().rev() {
                    t.extend(match rhs_binding {
                        Some(ref rbind) => {
                            quote! {
                                let #rbind = value_stack.pop().unwrap();
                            }
                        }
                        None => {
                            // The rule has no binding for this value.  Pop it from the stack and discard it.
                            quote! {
                                value_stack.pop();
                            }
                        }
                    })
                }
                t.extend(quote! {#block});
                t
            }
            None => {
                // This reduction does not have any code to execute.  Still, we need to
                // remove items from the value stack.
                // println!("no action");
                let num_rhs = gram.get_rhs_items(rule).len();
                let mut t = TokenStream::new();
                for _ in 0..num_rhs {
                    t.extend(quote! {
                        value_stack.pop();
                    });
                }
                t
            }
        };

        let pat_value: usize = rule_i - 2;
        let rule_str = gram.rule_to_str(rule);
        action_arms.extend(quote! {
            #pat_value => {
                // log::debug!("reduce: {}", #rule_str);
                log_reduction(#rule_i, #rule_str);
                #stmts
            }
        });
    }

    items.extend(quote! {
    fn reduce(
        value_stack: &mut Vec<#symbol_value_ty>,
        reduction: usize,
        #context_param_ident: &mut #context_ty) -> #symbol_value_ty {

        fn log_reduction(rule: usize, reduction_text: &'static str) {
            log::debug!("reduction: {} {}", rule, reduction_text);
        }

        match reduction {
            #action_arms
            _ => unreachable!()
        }
    }

    fn new_parser() -> racc_runtime::ParserState<#symbol_value_ty, #context_ty> {
        racc_runtime::ParserState::new(get_parser_tables())
    }

    fn get_parser_tables() -> racc_runtime::ParserTables<#symbol_value_ty, #context_ty> {
        racc_runtime::ParserTables {
                yyrindex: &YYRINDEX,
                yygindex: &YYGINDEX,
                yysindex: &YYSINDEX,
                yytable: &YYTABLE,
                yydefred: &YYDEFRED,
                yylen: &YYLEN,
                yylhs: &YYLHS,
                yycheck: &YYCHECK,
                yydgoto: &YYDGOTO,
                yyname: &YYNAME,       // for debugging
                yyrules: &YYRULES,      // for debugging
                yyfinal: YYFINAL,
                reduce: reduce
            }
        }
    });

    items.extend(output_rule_data(gram));

    // Emit the YYLEN table.
    items.extend({
        let yylen: Vec<i16> = (2..gram.nrules)
            .map(|r| gram.rule_rhs_syms(Rule(r as i16)).len() as i16)
            .collect::<Vec<i16>>();
        make_table_i16(Ident::new("YYLEN", sp), &yylen)
    });

    // emit some tables just for debugging
    items.extend(make_symbol_names_table(sp, gram));

    items.extend(make_rule_text_table(sp, gram));

    items
}

// Generates the YYLHS table.
fn output_rule_data(gram: &Grammar) -> TokenStream {
    let mut data: Vec<i16> = Vec::new();
    data.push(gram.value[gram.start().index()]);
    for i in 3..gram.nrules {
        data.push(gram.value[gram.rlhs[i].0 as usize]);
    }
    make_table_i16(Ident::new("YYLHS", Span::call_site()), &data)
}

fn make_symbol_names_table(span: Span, gram: &Grammar) -> TokenStream {
    // The values used at runtime are not symbol indices.  They are token values, which come from gram.value[token].value.
    // This is ugly and inefficient.

    let mut max_value: i16 = i16::MIN;
    for i in 0..gram.ntokens {
        max_value = cmp::max(max_value, gram.value[i]);
    }

    assert!(max_value >= 0);
    assert!(max_value < i16::MAX);
    let length = (max_value + 1) as usize;

    let mut toknames: Vec<String> = vec![String::new(); length];

    // Now put the names into proper places.
    for (value, name) in gram.value[0..gram.ntokens]
        .iter()
        .zip(gram.name[0..gram.ntokens].iter())
    {
        toknames[*value as usize] = name.to_string();
    }

    make_table_string(Ident::new("YYNAME", span), &toknames)
}

fn make_table_string(name: Ident, strings: &[String]) -> TokenStream {
    let strings_len = strings.len();
    let strings: Vec<syn::LitStr> = strings
        .iter()
        .map(|s| syn::LitStr::new(s, name.span()))
        .collect();
    quote! {
        static #name: [&str; #strings_len] = [
            #( #strings ),*
        ];
    }
}

fn make_rule_text_table(span: Span, gram: &Grammar) -> TokenStream {
    let rules: Vec<String> = (2..gram.nrules)
        .map(|rule| gram.rule_to_str(Rule(rule as i16)))
        .collect();
    make_table_string(Ident::new("YYRULES", span), &rules)
}

fn make_table_i16(name: Ident, values: &[i16]) -> TokenStream {
    make_table_i16_as_u16(name, values)
}

#[allow(dead_code)]
fn make_table_i16_real(name: Ident, values: &[i16]) -> TokenStream {
    let values_len = values.len();
    quote! {
        static #name: [i16; #values_len] = [
            #(
                #values
            ),*
        ];
    }
}

// yuck
fn make_table_i16_as_u16(name: Ident, values: &[i16]) -> TokenStream {
    let u_values: Vec<u16> = values.iter().map(|&value| value as u16).collect();

    let values_len = u_values.len();
    quote! {
        static #name: [u16; #values_len] = [
            #(
                #u_values
            ),*
        ];
    }
}

fn output_actions(
    span: Span,
    gram: &Grammar,
    gotos: &GotoMap,
    parser: &YaccParser,
) -> Vec<TokenStream> {
    let nstates = parser.nstates();

    let mut act = ActionsTable::new(nstates, gram.nvars);

    token_actions(gram, parser, &mut act);
    let dgoto = goto_actions(gram, nstates, gotos, &mut act);
    let (nentries, order) = sort_actions(&mut act);

    let packed = pack_table(parser.nstates(), nentries, &order, &act);

    let mut items: Vec<TokenStream> = Vec::new();
    // debug!("emitting tables");
    items.push(make_table_i16(Ident::new("YYDGOTO", span), &dgoto));

    // was output_base
    items.push(make_table_i16(
        Ident::new("YYSINDEX", span),
        &packed.base[..nstates],
    ));
    items.push(make_table_i16(
        Ident::new("YYRINDEX", span),
        &packed.base[nstates..nstates * 2],
    ));
    items.push(make_table_i16(
        Ident::new("YYGINDEX", span),
        &packed.base[nstates * 2..act.nvectors],
    ));

    // was output_table
    // todo, emit const YYTABLESIZE = m_high
    items.push(make_table_i16(
        Ident::new("YYTABLE", span),
        &packed.table[..packed.high + 1],
    ));

    // was output_check
    items.push(make_table_i16(
        Ident::new("YYCHECK", span),
        &packed.check[..packed.high + 1],
    ));

    items
}

struct ActionsTable {
    /// nvectors = 2 * nstates + gram.nvars
    nvectors: usize,

    // len = nvectors
    // tally[0..nstates] =  shift_count for each state
    // tally[nstates..nstates * 2] = reduce_count for each  state
    // actually, it seems more complex than that
    tally: Vec<i16>,

    // len = nstates *  2
    width: Vec<i16>,
    froms: Vec<Vec<StateOrRule>>,
    tos: Vec<Vec<StateOrRule>>,
}
impl ActionsTable {
    pub fn new(nstates: usize, nvars: usize) -> Self {
        let nvectors = 2 * nstates + nvars;
        Self {
            nvectors: nvectors,
            tally: vec![0; nvectors],
            width: vec![0; nvectors],
            froms: vec![Vec::new(); nvectors],
            tos: vec![Vec::new(); nvectors],
        }
    }
}

fn token_actions(gram: &Grammar, parser: &YaccParser, act: &mut ActionsTable)  {
    debug!("token_actions()");

    let nstates = parser.nstates();
    let mut actionrow: Vec<i16> = vec![0; 2 * gram.ntokens]; // contains EITHER Rule or State

    for (i, actions) in parser.actions.iter().enumerate() {
        if actions.len() != 0 {
            debug!("    state={}", i);
            for ii in actionrow.iter_mut() {
                *ii = 0;
            }

            let mut shiftcount: usize = 0;
            let mut reducecount: usize = 0;
            for p in actions.iter() {
                if p.suppressed == 0 {
                    match p.action_code {
                        ActionCode::Shift(to_state) => {
                            shiftcount += 1;
                            actionrow[p.symbol.0 as usize] = to_state.0;
                            // debug!("        shift {}", p.number);
                        }
                        ActionCode::Reduce(reduce_rule) => {
                            if reduce_rule != parser.default_reductions[i] {
                                reducecount += 1;
                                actionrow[(p.symbol.0 as usize) + gram.ntokens] = reduce_rule.0;
                                // debug!("        reduce {}", p.number);
                            }
                        }
                    }
                }
            }

            debug!(
                "        shiftcount={} reducecount={}",
                shiftcount, reducecount
            );

            act.tally[i] = shiftcount as i16;
            act.tally[nstates + i] = reducecount as i16;
            act.width[i] = 0;
            act.width[nstates + i] = 0;

            if shiftcount > 0 {
                let mut r: Vec<i16> = Vec::with_capacity(shiftcount);
                let mut s: Vec<i16> = Vec::with_capacity(shiftcount);
                let mut min = i16::MAX;
                let mut max = 0;
                for j in 0..gram.ntokens {
                    if actionrow[j] != 0 {
                        min = cmp::min(min, gram.value[j]);
                        max = cmp::max(max, gram.value[j]);
                        r.push(gram.value[j]);
                        s.push(actionrow[j]);
                        debug!(
                            "        shift for token {} {}, pushing r={} s={}",
                            j, gram.name[j], gram.value[j], actionrow[j]
                        );
                    }
                }
                act.froms[i] = r;
                act.tos[i] = s;
                act.width[i] = max - min + 1;
            }

            if reducecount > 0 {
                let mut r: Vec<i16> = Vec::with_capacity(reducecount);
                let mut s: Vec<i16> = Vec::with_capacity(reducecount);
                let mut min = i16::MAX;
                let mut max = 0;
                for j in 0..gram.ntokens {
                    if actionrow[gram.ntokens + j] != 0 {
                        min = cmp::min(min, gram.value[j]);
                        max = cmp::max(max, gram.value[j]);
                        r.push(gram.value[j]);
                        s.push(actionrow[gram.ntokens + j] - 2);
                        debug!(
                            "        reduce for token {} {}, pushing r={} s={}",
                            j,
                            gram.name[j],
                            gram.value[j],
                            actionrow[gram.ntokens + j] - 2
                        );
                    }
                }
                act.froms[nstates + i] = r;
                act.tos[nstates + i] = s;
                act.width[nstates + i] = max - min + 1;
            }
        } else {
            debug!("    state={} has no actions", i);
        }
    }
}

// build the "dgoto" table
fn goto_actions(
    gram: &Grammar,
    nstates: usize,
    gotos: &GotoMap,
    act: &mut ActionsTable,
) -> Vec<StateOrRule> {
    debug!("goto_actions");
    let mut state_count: Vec<i16> = vec![0; nstates]; // temporary data, used in default_goto()
    let mut dgoto_table: Vec<StateOrRule> = Vec::with_capacity(gram.nvars); // the table that we are building
    for s in gram.iter_var_syms().skip(1) {
        let k = default_goto(gram, gotos, s, &mut state_count);
        dgoto_table.push(k.0);
        save_column(gram, nstates, gotos, s, k, act);
    }
    dgoto_table
}

/// Compute the default goto for a given symbol
/// state_count - a temporary table that can be used by this fn. contents when the function
/// is called are undefined. length  = nstates.
fn default_goto(gram: &Grammar, gotos: &GotoMap, symbol: Symbol, state_count: &mut [i16]) -> State {
    let var_gotos = gotos.values(gram.symbol_to_var(symbol));
    if var_gotos.is_empty() {
        return State(0);
    }

    for c in state_count.iter_mut() {
        *c = 0;
    }

    for &entry in var_gotos.iter() {
        state_count[entry.to_state.0 as usize] += 1;
    }

    let mut max = 0;
    let mut default_state = 0;
    for (state, &count) in state_count.iter().enumerate() {
        if count > max {
            max = count;
            default_state = state;
        }
    }

    debug!("default_goto({}) = {}", symbol, default_state);
    State(default_state as i16)
}

fn save_column(
    gram: &Grammar,
    nstates: usize,
    gotos: &GotoMap,
    symbol: Symbol,
    default_state: State,
    act: &mut ActionsTable,
) {
    let symbol_gotos = gotos.values(gram.symbol_to_var(symbol));
    debug!(
        "save_column: symbol={} default_state={} symbol_gotos={:?}",
        symbol, default_state, symbol_gotos
    );

    let mut count: usize = 0;
    for &entry in symbol_gotos.iter() {
        if entry.to_state != default_state {
            // debug!("    to_state[{}]={}", i, entry.to_state);
            count += 1;
        }
    }
    if count == 0 {
        debug!("    none");
        return;
    }

    let mut spf: Vec<StateOrRule> = Vec::with_capacity(count);
    let mut spt: Vec<StateOrRule> = Vec::with_capacity(count);
    for &entry in symbol_gotos.iter() {
        if entry.to_state != default_state {
            spf.push(entry.from_state.0);
            spt.push(entry.to_state.0);
        }
    }

    let symno = (gram.value[symbol.0 as usize] as usize) + 2 * nstates;
    let spf_width = spf[spf.len() - 1] - spf[0] + 1;
    act.froms[symno] = spf;
    act.tos[symno] = spt;
    act.tally[symno] = count as i16;
    act.width[symno] = spf_width;
    debug!(
        "    tally[{}]={} width[{}]={}",
        symno, act.tally[symno], symno, act.width[symno]
    );
}

fn sort_actions(act: &ActionsTable) -> (usize, Vec<usize>) {
    debug!("sort_actions() nvectors={}", act.nvectors);

    let mut order: Vec<usize> = vec![0; act.nvectors];
    let mut nentries: isize = 0;

    for i in 0..act.nvectors {
        debug!("tally[{}]={}", i, act.tally[i]);
        if act.tally[i] > 0 {
            let t = act.tally[i];
            let w = act.width[i];
            let mut j: isize = nentries - 1;
            debug!("    t={} w={} j={}", t, w, j);

            while j >= 0 && (act.width[order[j as usize]] < w) {
                j -= 1;
                debug!("    j-- to {}, because width < w", j);
            }

            while j >= 0
                && (act.width[order[j as usize]] == w)
                && (act.tally[order[j as usize]] < t)
            {
                j -= 1;
                debug!("    j-- to {}, because tally < t", j);
            }

            let mut k = nentries - 1;
            while k > j {
                debug!(
                    "        order[{}] = order[{}] = {} (shifting)",
                    (k + 1) as usize,
                    k as usize,
                    order[k as usize]
                );
                order[(k + 1) as usize] = order[k as usize];
                k -= 1;
            }

            debug!("        order[{}] = {}", (j + 1) as usize, i);
            order[(j + 1) as usize] = i;
            nentries += 1;
        }
    }

    debug!("order:");
    for &n in order.iter() {
        debug!("    {}", n);
    }
    debug!("nentries={}", nentries);

    (nentries as usize, order)
}

// The function matching_vector determines if the vector specified by
// the input parameter matches a previously considered vector. The
// test at the start of the function checks if the vector represents
// a row of shifts over terminal symbols or a row of reductions, or a
// column of shifts over a nonterminal symbol.  Berkeley Yacc does not
// check if a column of shifts over a nonterminal symbols matches a
// previously considered vector.  Because of the nature of LR parsing
// tables, no two columns can match.  Therefore, the only possible
// match would be between a row and a column.  Such matches are
// unlikely.  Therefore, to save time, no attempt is made to see if a
// column matches a previously considered vector.
//
// Matching_vector is poorly designed.  The test could easily be made
// faster.  Also, it depends on the vectors being in a specific
// order.
fn matching_vector(pack: &PackState<'_>, vector: usize) -> Option<usize> {
    let i = pack.order[vector];
    if i >= 2 * pack.nstates {
        debug!("    matching_vector: vector={} no match", vector);
        return None;
    }

    let act = pack.act;
    let t = act.tally[i];
    let w = act.width[i];

    for &j in pack.order[0..vector].iter().rev() {
        if act.width[j] != w || act.tally[j] != t {
            return None;
        }

        let t = t as usize;
        let is_match = act.tos[i][..t] == act.tos[j][..t] && act.froms[i][..t] == act.froms[j][..t];
        if is_match {
            debug!("    matching_vector: vector={} matches at {}", vector, j);
            return Some(j);
        }
    }

    debug!("    matching_vector: vector={} - no match", vector);
    return None;
}

fn pack_vector(pack: &mut PackState<'_>, vector: usize) -> isize {
    // debug!("pack_vector: vector={} lowzero={}", vector, pack.lowzero);
    let act = pack.act;
    let i = pack.order[vector];
    let t = act.tally[i] as usize;
    assert!(t != 0);

    let from = &act.froms[i];
    let to = &act.tos[i];

    // debug!("from[0]={}", from[0]);

    let mut j: isize = (pack.lowzero as isize) - (from[0] as isize);
    // debug!("j={}", j);
    for &f in from[1..t].iter() {
        if (pack.lowzero as isize) - (f as isize) > j {
            j = (pack.lowzero as isize) - (f as isize);
            // debug!("j={}", j);
        }
    }

    loop {
        // debug!("    loop: j={}", j);
        if j == 0 {
            j = 1;
            continue;
        }

        let mut ok = true;
        for &f in &from[0..t] {
            let loc = (j + (f as isize)) as usize;

            // make sure we can read/write table[loc] and table[check]
            if loc > pack.table.len() {
                assert!(pack.table.len() == pack.check.len());
                let grow = loc + 1 - pack.table.len();
                debug!("        growing table/check by {}", grow);
                pack.table.extend(repeat(0).take(grow));
                pack.check.extend(repeat(-1).take(grow));
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
        for k in 0..vector {
            if pack.pos[k] as isize == j {
                ok = false;
                break;
            }
        }
        if !ok {
            j += 1;
            continue;
        }

        for k in 0..t {
            let loc = (j + (from[k] as isize)) as usize;
            pack.table[loc] = to[k];
            pack.check[loc] = from[k];
            if loc > pack.high {
                pack.high = loc;
            }
        }

        while pack.check[pack.lowzero] != -1 {
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
    lowzero: usize,
    high: usize,

    order: &'a [usize],
    nstates: usize,
    act: &'a ActionsTable,
}

fn pack_table<'a>(
    nstates: usize,
    nentries: usize,
    order: &'a [usize],
    act: &'a ActionsTable,
) -> PackState<'a> {
    debug!("pack_table: nentries={}", nentries);

    let initial_maxtable = 1000;

    let mut pack = PackState {
        base: vec![0; act.nvectors],
        pos: vec![0; nentries],
        table: vec![0; initial_maxtable],
        check: vec![-1; initial_maxtable],
        lowzero: 0,
        high: 0,
        order: order,
        nstates: nstates,
        act: act,
    };

    for i in 0..nentries {
        let place: isize = match matching_vector(&pack, i) {
            Some(state) => pack.base[state] as isize,
            None => pack_vector(&mut pack, i),
        };

        pack.pos[i] = place as i16;
        pack.base[order[i]] = place as i16;
    }

    pack
}
