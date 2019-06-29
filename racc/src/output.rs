#![allow(unused_imports)]
#![allow(dead_code)]

use syn::ItemStatic;
use syn::ItemConst;
use syn::LitInt;

use std::cmp;
use syn::{Arm, Item,  Type, Stmt, Pat, Block, WhereClause, Generics};
use syn::token::{Where};
use syn::punctuated::Punctuated;
use proc_macro2::{Span, TokenStream};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{Expr, ExprBlock, Ident, Token};

use std::iter::repeat;
use crate::grammar::Grammar;
use crate::mkpar::{ActionCode, YaccParser};
use crate::lalr::GotoMap;
use quote::quote;
use log::debug;

const I16_MAX: i16 = 0x7fff;
const I16_MIN: i16 = -0x8000;

struct ActionsTable {
    nvectors: usize,
    tally: Vec<i16>,
    width: Vec<i16>,
    froms: Vec<Vec<i16>>,
    tos: Vec<Vec<i16>>
}

fn no_generics() -> Generics {
     Generics {
        lt_token: None,
        params: Punctuated::new(),
        gt_token: None,
        where_clause: None
    }
}

/*
fn no_where() -> WhereClause {
    WhereClause {
        where_token: syn::token::Where(),
        predicates: Punctuated::new()
    }
}
*/

use syn::export::quote::ToTokens;

// Given a constructed parser (a description of a state machine which parses
// a given grammar), produces a Rust AST which implements the parser.
pub fn output_parser_to_ast(
    gram: &Grammar,
    gotos: &GotoMap,
    parser: &YaccParser,
    blocks: &[Option<Block>],
    rhs_binding: &[Option<Ident>],
    context_ty: Type,                      // Ident to use for the context type, passed to the reduce() method
    context_param_ident: Ident,            // Ident to use for the context arg, passed to the reduce() method
    symbol_value_ty: Type,                 // type to use for value_stack
    ) -> TokenStream {

    assert!(blocks.len() == gram.nrules);

    let grammar_span = Span::call_site();
    let sp = grammar_span;

    let mut items: TokenStream = TokenStream::new();

    //  Generate YYDEFRED table.
    let yydefred: Vec<i16> = parser.default_reductions.iter().map(|s| if *s != 0 { *s - 2 } else { 0 }).collect();
    items.extend({
        make_table_i16(Ident::new("YYDEFRED", sp), &yydefred)
    });

    items.extend(output_actions(grammar_span, gram, gotos, parser));
    // println!("output_actions done");

    for t in 1..gram.ntokens {
        // todo: use the original Ident from parsing, for better error reporting
        let tokvalue = gram.value[t] as u32;
        let tok_ident = Ident::new(&gram.name[t], Span::call_site()); // TODO: use original Ident from parser i nput
        items.extend(quote!(const #tok_ident: u32 = #tokvalue;));
    }
    // println!("tokens consts done");

    // Generate YYFINAL constant.
    let yyfinal = parser.final_state;
    items.extend(quote!{
        const YYFINAL: usize = #yyfinal;
    });

    // Build up actions
    let mut action_arms: TokenStream = TokenStream::new();
    let mut rule_iter: usize = 0;
    for block in blocks.iter() {
        let rule = rule_iter;
        rule_iter += 1;

        if rule < 3 {
            continue;
        }

        // Based on the rule we are reducing, get values from the value stack,
        // and bind them as a tuple named 'args'.
        let mut stmts: TokenStream = TokenStream::new();

        // stmts.push(parse_stmt(format!("debug!(\"{}\");", gram.rule_to_str(rule))));

        let final_expr: Option<Expr> = match block {
            Some(block) => {
                // We need to pop items off the stack and associate them with variables from right to left.
                let rhs_index = gram.rrhs[rule] as usize;
                let rhs = gram.get_rhs_items(rule);
                for i in (0..rhs.len()).rev() {
                    match &rhs_binding[rhs_index + i] {
                        Some(ref rbind) => {
                            // println!("rhs binding: {:?}", rbind);
                            stmts.extend(quote!{
                                let #rbind = value_stack.pop().unwrap();
                            });
                            // println!(".");
                        }
                        None => {
                            // println!("rhs binding: <none>");
                            // The rule has no binding for this value.  Pop it from the stack and discard it.
                            stmts.extend(quote!{
                                drop(value_stack.pop());
                                });
                        }
                    }
                }
                // println!("passing through block");
                let rr = Some(Expr::Block(ExprBlock { block: block.clone(), attrs:vec![], label: None }));
                rr
            }
            None => {
                // This reduction does not have any code to execute.  Still, we need to
                // remove items from the value stack.
                // println!("no action");
                for _ in gram.get_rhs_items(rule).iter() {
                    stmts.extend(quote!{
                        drop(value_stack.pop());
                    });
                }
                None
            }
        };

        let pat_value = rule - 2;
        let rule_str = gram.rule_to_str(rule);
        action_arms.extend(
            quote!{
                #pat_value => {
                    log::debug!("{}", #rule_str);
                    #stmts;
                    #final_expr
                }
            }
        );
    }

    items.extend(
        quote!{
            fn reduce(
                // Arg::new_self(sp, Mutability::MutImmutable, ident_of("self")),
                value_stack: &mut Vec<#symbol_value_ty>,
                reduction: usize,
                #context_param_ident: &mut #context_ty) -> #symbol_value_ty {
                match reduction {
                    #action_arms
                    _ => unreachable!()
                }
            }
        });
    // println!("fn reduce is ok");
    items.extend(
        quote!{
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
            }
        );
    // println!("fn get_parser_tables is ok");

    items.extend(output_rule_data(gram));
    // println!("output_rule_data is ok");

    // Emit the YYLEN table.
    items.extend({
        let yylen: Vec<i16> = (2..gram.nrules).map(|r| gram.rrhs[r + 1] - gram.rrhs[r] - 1).collect();
        make_table_i16(Ident::new("YYLEN", sp), &yylen)
    });
    // println!("YYLEN is ok");

    // emit some tables just for debugging
    items.extend(make_symbol_names_table(sp, gram));
    // println!("make_symbol_names_table is ok");

    items.extend(make_rule_text_table(sp, gram));
    // println!("make_rule_text_table is ok");

    // println!("{}", items);

    items
}

// Generates the YYLHS table.
fn output_rule_data(gram: &Grammar) -> TokenStream {
    let mut data: Vec<i16> = Vec::new();
    data.push(gram.value[gram.start_symbol]);
    for i in 3..gram.nrules {
        data.push(gram.value[gram.rlhs[i] as usize]);
    }
    make_table_i16(Ident::new("YYLHS", Span::call_site()), &data)
}

fn make_symbol_names_table(span: Span, gram: &Grammar) -> TokenStream {
    // The values used at runtime are not symbol indices.  They are token values, which come from gram.value[token].value.
    // This is ugly and inefficient.

    let mut max_value: i16 = I16_MIN;
    for i in 0..gram.ntokens {
        max_value = cmp::max(max_value, gram.value[i]);
    }

    assert!(max_value >= 0);
    assert!(max_value < I16_MAX);
    let length = (max_value + 1) as usize;

    let mut toknames: Vec<String> = repeat(String::new()).take(length).collect();
    
    // Now put the names into proper places.
    for i in 0..gram.ntokens {
        toknames[gram.value[i] as usize] = gram.name[i].clone();
    }

    make_table_string(Ident::new("YYNAME", span), &toknames)
}

fn make_table_string(name: Ident, strings: &[String]) -> TokenStream {
    let strings_len = strings.len();
    let strings: Vec<syn::LitStr> = strings.iter().map(|s|  syn::LitStr::new(s,  name.span())).collect();
    quote!{
        static #name: [&str; #strings_len] = [
            #( #strings ),*
        ];
    }

}

fn make_rule_text_table(span: Span, gram: &Grammar) -> TokenStream {
    let rules: Vec<String> = (2..gram.nrules).map(|rule| gram.rule_to_str(rule)).collect();
    make_table_string(Ident::new("YYRULES", span), &rules)
}

/*
#[allow(dead_code)]
fn make_table_usize(name: Ident, values: &[usize]) -> Item {
    let values_expr = cx.expr_vec(span, values.iter().map(|value| expr_usize(span, *value)).collect());
    let ty_usize = quote!(usize);
    let table_ident = cx.ident_of(name);
    let table_ty = cx.ty(span, Ty_::TyFixedLengthVec(ty_usize, cx.expr_usize(span, values.len())));
    let table_item = cx.item_static(span, table_ident, table_ty, Mutability::MutImmutable, values_expr);
    // debug!("built table item for '{}': values {}", name, values);
    // debug!("item: {}", pprust::item_to_string(&*table_item));
    table_item
}
*/

fn make_table_i16(name: Ident, values: &[i16]) -> TokenStream {
    make_table_i16_as_u16(name, values)
}

fn make_table_i16_real(name: Ident, values: &[i16]) -> TokenStream {
    let values_len = values.len();
    quote!{
        static #name: [i16; #values_len] = [
            #(
                #values
            ),*
        ];
    }

/*
    let values_expr = cx.expr_vec(span, values.iter().map(|value| expr_i16(cx, span, *value)).collect());
    let ty_i16 = quote!(i16);
    let table_ident = cx.ident_of(name);
    let table_ty = cx.ty(span, Ty_::TyFixedLengthVec(ty_i16, cx.expr_usize(span, values.len())));
    let table_item = cx.item_static(span, table_ident, table_ty, Mutability::MutImmutable, values_expr);
    // debug!("built table item for '{}': values {}", name, values);
    // debug!("item: {}", pprust::item_to_string(&*table_item));
    table_item
    */
}

// yuck
fn make_table_i16_as_u16(name: Ident, values: &[i16]) -> TokenStream {
    let u_values: Vec<u16> = values.iter().map(|&value| value as u16).collect();

    let values_len = u_values.len();
    quote!{
        static #name: [u16; #values_len] = [
            #(
                #u_values
            ),*
        ];
    }

/*
    let values_expr = cx.expr_vec(span, values.iter().map(|value| expr_u16(cx, span, *value as u16)).collect());
    let ty_u16 = quote!(u16);
    let table_ident = cx.ident_of(name);
    let table_ty = cx.ty(span, Ty_::TyFixedLengthVec(ty_u16, cx.expr_usize(span, values.len())));
    let table_item = cx.item_static(span, table_ident, table_ty, Mutability::MutImmutable, values_expr);
    table_item
    */
}

fn output_actions(span: Span, gram: &Grammar, gotos: &GotoMap, parser: &YaccParser) -> Vec<TokenStream> {
    // debug!("output_actions");

    let nstates = parser.nstates;

    let mut act = token_actions(gram, parser);
    let dgoto = goto_actions(gram, nstates, gotos, &mut act);
    let (nentries, order) = sort_actions(&mut act);
    
    let packed = pack_table(parser.nstates, nentries, &order, &act);

    let mut items: Vec<TokenStream> = Vec::new();
    // debug!("emitting tables");
    items.push(make_table_i16(Ident::new("YYDGOTO", span), &dgoto));

    // was output_base
    items.push(make_table_i16(Ident::new("YYSINDEX", span), &packed.base[.. nstates]));
    items.push(make_table_i16(Ident::new("YYRINDEX", span), &packed.base[nstates .. nstates * 2]));
    items.push(make_table_i16(Ident::new("YYGINDEX", span), &packed.base[nstates * 2 .. act.nvectors]));

    // was output_table
    // todo, emit const YYTABLESIZE = m_high
    items.push(make_table_i16(Ident::new("YYTABLE", span), &packed.table[.. packed.high + 1]));

    // was output_check
    items.push(make_table_i16(Ident::new("YYCHECK", span), &packed.check[.. packed.high + 1]));

    items
}

fn token_actions(gram: &Grammar, parser: &YaccParser) -> ActionsTable {
    debug!("token_actions()");

    let nstates = parser.nstates;
    let nvectors = 2 * nstates + gram.nvars;
    let mut tally: Vec<i16> = vec![0; nvectors];
    let mut width: Vec<i16> = vec![0; nvectors];
    let mut froms: Vec<Vec<i16>> = repeat(Vec::new()).take(nvectors).collect();
    let mut tos: Vec<Vec<i16>> = repeat(Vec::new()).take(nvectors).collect();
    let mut actionrow: Vec<i16> = vec![0; 2 * gram.ntokens];

    for i in 0..nstates {
        let actions = &parser.actions[i];
        if actions.len() != 0 {
            debug!("    state={}", i);
            for ii in actionrow.iter_mut() {
                *ii = 0;
            }

            let mut shiftcount: usize = 0;
            let mut reducecount: usize = 0;
            for p in actions.iter() {
                if p.suppressed == 0 {
                    if p.action_code == ActionCode::Shift {
                        shiftcount += 1;
                        actionrow[p.symbol as usize] = p.number;
                        // debug!("        shift {}", p.number);
                    }
                    else if p.action_code == ActionCode::Reduce && p.number != parser.default_reductions[i] {
                        reducecount += 1;
                        actionrow[(p.symbol as usize) + gram.ntokens] = p.number;
                        // debug!("        reduce {}", p.number);
                    }
                }
            }

            debug!("        shiftcount={} reducecount={}", shiftcount, reducecount);

            tally[i] = shiftcount as i16;
            tally[nstates + i] = reducecount as i16;
            width[i] = 0;
            width[nstates + i] = 0;

            if shiftcount > 0 {
                let mut r: Vec<i16> = Vec::with_capacity(shiftcount);
                let mut s: Vec<i16> = Vec::with_capacity(shiftcount);
                let mut min = I16_MAX;
                let mut max = 0;
                for j in 0..gram.ntokens {
                    if actionrow[j] != 0 {
                        min = cmp::min(min, gram.value[j]);
                        max = cmp::max(max, gram.value[j]);
                        r.push(gram.value[j]);
                        s.push(actionrow[j]);
                        debug!("        shift for token {} {}, pushing r={} s={}", j, gram.name[j], gram.value[j], actionrow[j]);
                    }
                }
                froms[i] = r;
                tos[i] = s;
                width[i] = max - min + 1;
            }

            if reducecount > 0 {
                let mut r: Vec<i16> = Vec::with_capacity(reducecount);
                let mut s: Vec<i16> = Vec::with_capacity(reducecount);
                let mut min = I16_MAX;
                let mut max = 0;
                for j in 0..gram.ntokens {
                    if actionrow[gram.ntokens + j] != 0 {
                        min = cmp::min(min, gram.value[j]);
                        max = cmp::max(max, gram.value[j]);
                        r.push(gram.value[j]);
                        s.push(actionrow[gram.ntokens + j] - 2);
                        debug!("        reduce for token {} {}, pushing r={} s={}", j, gram.name[j], gram.value[j], actionrow[gram.ntokens + j] - 2);
                    }
                }
                froms[nstates + i] = r;
                tos[nstates + i] = s;
                width[nstates + i] = max - min + 1;
            }
        }
        else {
            debug!("    state={} has no actions", i);
        }
    }

    ActionsTable {
        nvectors: nvectors,
        tally: tally,
        width: width,
        froms: froms,
        tos: tos
    }
}

fn default_goto(
    gram: &Grammar,
    gotos: &GotoMap,
    symbol: usize,
    nstates: usize,
    state_count: &mut Vec<i16>) -> usize
{
    let m = gotos.goto_map[symbol - gram.ntokens] as usize;
    let n = gotos.goto_map[symbol - gram.ntokens + 1] as usize;
    if m == n {
        return 0;
    }

    for i in 0..nstates {
        state_count[i] = 0;
    }

    for i in m..n {
        state_count[gotos.to_state[i] as usize] += 1;
    }

    let mut max = 0;
    let mut default_state = 0;
    for i in 0..nstates {
        if state_count[i] > max {
            max = state_count[i];
            default_state = i;
        }
    }

    debug!("default_goto({}) = {}", symbol, default_state);

    default_state
}

fn save_column(
    gram: &Grammar, 
    nstates: usize,
    gotos: &GotoMap,
    symbol: usize, 
    default_state: usize,
    act: &mut ActionsTable)
{
    let m = gotos.goto_map[symbol - gram.ntokens] as usize;
    let n = gotos.goto_map[symbol - gram.ntokens + 1] as usize;
    debug!("save_column: symbol={} default_state={} m={} n={}", symbol, default_state, m, n);

    let mut count: usize = 0;
    for i in m..n {
        if (gotos.to_state[i] as usize) != default_state {
            debug!("    to_state[{}]={}", i, gotos.to_state[i]);
            count += 1;
        }
    }
    if count == 0 {
        debug!("    none");
        return;
    }


    let mut spf: Vec<i16> = Vec::with_capacity(count);
    let mut spt: Vec<i16> = Vec::with_capacity(count);
    for i in m..n {
        if (gotos.to_state[i] as usize) != default_state {
            spf.push(gotos.from_state[i]);
            spt.push(gotos.to_state[i]);
        }
    }

    let symno = (gram.value[symbol] as usize) + 2 * nstates;
    let spf_width = spf[spf.len() - 1] - spf[0] + 1;
    act.froms[symno] = spf;
    act.tos[symno] = spt;
    act.tally[symno] = count as i16;
    act.width[symno] = spf_width;
    debug!("    tally[{}]={} width[{}]={}", symno, act.tally[symno], symno, act.width[symno]);
}

// build the "dgoto" table
fn goto_actions(gram: &Grammar, nstates: usize, gotos: &GotoMap, act: &mut ActionsTable) -> Vec<i16> {
    debug!("goto_actions");

    let mut state_count: Vec<i16> = repeat(0).take(nstates).collect();         // temporary data, used in default_goto()
    let mut dgoto_table: Vec<i16> = Vec::with_capacity(gram.nvars);    // the table that we are building

    let k = default_goto(gram, gotos, gram.start_symbol + 1, nstates, &mut state_count);
    dgoto_table.push(k as i16);
    save_column(gram, nstates, gotos, gram.start_symbol + 1, k, act);

    for i in (gram.start_symbol + 2)..gram.nsyms {
        let k = default_goto(gram, gotos, i, nstates, &mut state_count);
        dgoto_table.push(k as i16);
        save_column(gram, nstates, gotos, i, k, act);
    }

    dgoto_table
}

fn sort_actions(act: &ActionsTable) -> (usize, Vec<usize>) {
    debug!("sort_actions() nvectors={}", act.nvectors);

    let mut order: Vec<usize> = repeat(0).take(act.nvectors).collect();
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

            while j >= 0 && (act.width[order[j as usize]] == w) && (act.tally[order[j as usize]] < t) {
                j -= 1;
                debug!("    j-- to {}, because tally < t", j);
            }

            let mut k = nentries - 1;
            while k > j {
                debug!("        order[{}] = order[{}] = {} (shifting)", (k + 1) as usize, k as usize, order[k as usize]);
                order[(k + 1) as usize] = order[k as usize];
                k -= 1;
            }

            debug!("        order[{}] = {}", (j + 1) as usize, i);
            order[(j + 1) as usize] = i;
            nentries += 1;
        }
    }

    debug!("order:");
    for i in 0..order.len() {
        debug!("    {}", order[i]);
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
fn matching_vector(pack: &PackState, vector: usize) -> Option<usize>
{
    let i = pack.order[vector];
    if i >= 2 * pack.nstates {
        debug!("    matching_vector: vector={} no match", vector);
        return None;
    }

    let t = pack.act.tally[i];
    let w = pack.act.width[i];

    let act = pack.act;

    for prev in (0..vector).rev() {
        let j = pack.order[prev];
        if act.width[j] != w || act.tally[j] != t {
            return None;
        }

        let mut is_match = true;
        for k in 0..(t as usize) {
            if act.tos[j][k] != act.tos[i][k] || act.froms[j][k] != act.froms[i][k] {
                is_match = false;
                break;
            }
        }
        if is_match {
            debug!("    matching_vector: vector={} matches at {}", vector, j);
            return Some(j);
        }
    }

    debug!("    matching_vector: vector={} - no match", vector);
    return None;
}

fn pack_vector(pack: &mut PackState, vector: usize) -> isize {
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
    table: Vec<i16>,        // table and check always have same len
    check: Vec<i16>,        // table is 0-filled, check is -1-filled
    lowzero: usize,
    high: usize,

    // read-only references to stuff
    order: &'a [usize],
    nstates: usize,
    act: &'a ActionsTable
}

fn pack_table<'a>(nstates: usize, nentries: usize, order: &'a [usize], act: &'a ActionsTable) -> PackState<'a> {
    debug!("pack_table: nentries={}", nentries);

    let initial_maxtable = 1000;

    let mut pack = PackState {
        base: repeat(0).take(act.nvectors).collect(),
        pos: repeat(0).take(nentries).collect(),
        table: repeat(0).take(initial_maxtable).collect(),
        check: repeat(-1).take(initial_maxtable).collect(),
        lowzero: 0,
        high: 0,
        order: order,
        nstates: nstates,
        act: act
    };

    for i in 0..nentries {
        // debug!("i={}", i);
        let place: isize = match matching_vector(&mut pack, i) {
            Some(state) => pack.base[state] as isize,
            None => pack_vector(&mut pack, i)
        };

        // debug!("    place={}", place);
        pack.pos[i] = place as i16;
        pack.base[order[i]] = place as i16;
    }

    pack
}
