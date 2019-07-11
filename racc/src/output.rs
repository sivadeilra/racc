use crate::grammar::Grammar;
use crate::lalr::GotoMap;
use crate::mkpar::{ActionCode, YaccParser};
use crate::util::fill_copy;
use crate::{Rule, State, StateOrRule};
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

    let default_reductions = crate::mkpar::default_reductions(&parser.actions);

    //  Generate YYDEFRED table.
    let yydefred: Vec<i16> = default_reductions
        .iter()
        .map(|&s| if s != Rule(0) { s.0 - 2 } else { 0 })
        .collect();
    items.extend(make_table_i16(Ident::new("YYDEFRED", sp), &yydefred));

    items.extend(output_actions(
        grammar_span,
        gram,
        gotos,
        parser,
        &default_reductions,
    ));

    for t in 1..gram.ntokens {
        let tokvalue = gram.value[t] as u16;
        let tok_ident = &gram.name[t];
        items.extend(quote!(const #tok_ident: u16 = #tokvalue;));
    }
    // println!("tokens consts done");

    // Generate YYFINAL constant.
    let yyfinal = parser.final_state.0 as u16;
    items.extend(quote! {
        const YYFINAL: u16 = #yyfinal;
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
    items.extend(make_table_i16(
        Ident::new("YYLEN", sp),
        &gram
            .iter_rules()
            .skip(2)
            .map(|r| gram.rule_rhs_syms(r).len() as i16)
            .collect::<Vec<i16>>(),
    ));

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

fn make_table_i16_signed(name: Ident, values: &[i16]) -> TokenStream {
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
    default_reductions: &[Rule],
) -> TokenStream {
    let nstates = parser.nstates();

    let mut act = ActionsTable::new(nstates, gram.nvars);

    token_actions(
        gram,
        parser,
        &default_reductions,
        &mut act.froms,
        &mut act.tos,
    );
    let default_goto_table = default_goto_table(nstates, gotos);
    goto_actions(
        gram,
        nstates,
        gotos,
        &default_goto_table,
        &mut act.froms,
        &mut act.tos,
    );
    let order = sort_actions(&mut act);
    let packed = packing::pack_table(parser.nstates(), &order, &act);

    let mut items = TokenStream::new();
    items.extend(make_table_i16(
        Ident::new("YYDGOTO", span),
        &default_goto_table.iter().map(|s| s.0).collect::<Vec<i16>>(),
    ));
    items.extend(make_table_i16_signed(
        Ident::new("YYSINDEX", span),
        &packed.base[..nstates],
    ));
    items.extend(make_table_i16(
        Ident::new("YYRINDEX", span),
        &packed.base[nstates..nstates * 2],
    ));
    items.extend(make_table_i16(
        Ident::new("YYGINDEX", span),
        &packed.base[nstates * 2..act.nvectors],
    ));
    items.extend(make_table_i16(Ident::new("YYTABLE", span), &packed.table));
    items.extend(make_table_i16(Ident::new("YYCHECK", span), &packed.check));
    items
}

/// All of the vectors defined in ActionsTable have the same length (nvectors)
/// and the indices are assigned in the same way.
///
/// * S: first region,  length = nstates, contains: shifts
/// * R: second region, length = nstates, contains: reduces
/// * V: third region,  length = nvars,   contains: var stuff
///
/// nvectors = sum of the lengths of these regions = 2 * nstates + gram.nvars
pub struct ActionsTable {
    /// nvectors = 2 * nstates + gram.nvars
    nvectors: usize,
    froms: Vec<Vec<StateOrRule>>,
    tos: Vec<Vec<StateOrRule>>,
}
impl ActionsTable {
    pub fn new(nstates: usize, nvars: usize) -> Self {
        let nvectors = 2 * nstates + nvars;
        Self {
            nvectors,
            froms: Vec::new(), // vec![Vec::new(); nvectors],
            tos: Vec::new(),   // vec![Vec::new(); nvectors],
        }
    }
    pub fn tally(&self, i: usize) -> usize {
        self.froms[i].len()
    }
    pub fn width(&self, i: usize) -> i16 {
        let f = &self.froms[i];
        if f.len() != 0 {
            f[f.len() - 1] - f[0] + 1
        } else {
            0
        }
    }
}

/// This builds actions for tokens.
///
/// NOTE: In the original code, this function computed the 'tally' and 'width'
/// tables. The 'tally' table is unnecessary in Rust, because the `len()` of
/// the generated 'froms' and 'tos' table gives the same information. But the
/// 'width' table is slightly more interesting. The 'width' table was computed
/// as `max(j) - min(j) + 1`, where `j` was the token being considered.
///
/// The new code just computes it as `froms.last() - froms.first() + 1`, which
/// should be the same value, as long as action.symbol is in increasing order.
/// (See commit 1cc0a3174406eb28f767af0b91fc850e9364aaf2 for the last code
/// based on the old algorithm.)
fn token_actions(
    gram: &Grammar,
    parser: &YaccParser,
    default_reductions: &[Rule],
    froms: &mut Vec<Vec<i16>>,
    tos: &mut Vec<Vec<StateOrRule>>,
) {
    // shifts
    for actions in parser.actions.iter_entries() {
        let mut shift_r: Vec<i16> = Vec::new();
        let mut shift_s: Vec<i16> = Vec::new();
        for action in actions.iter() {
            if action.suppressed == 0 {
                match action.action_code {
                    ActionCode::Shift(shift_to_state) => {
                        let token = action.symbol.index();
                        shift_r.push(gram.value[token]);
                        shift_s.push(shift_to_state.0);
                    }
                    ActionCode::Reduce(_) => {}
                }
            }
        }
        froms.push(shift_r);
        tos.push(shift_s);
    }

    // reduces
    for (state, actions) in parser.actions.iter_entries().enumerate() {
        let mut reduce_r: Vec<i16> = Vec::new();
        let mut reduce_s: Vec<i16> = Vec::new();
        for action in actions.iter() {
            if action.suppressed == 0 {
                match action.action_code {
                    ActionCode::Reduce(reduce_rule) => {
                        if reduce_rule != default_reductions[state] {
                            let token = action.symbol.index();
                            reduce_r.push(gram.value[token]);
                            reduce_s.push(reduce_rule.0 - 2);
                        }
                    }
                    ActionCode::Shift(_) => {}
                }
            }
        }
        froms.push(reduce_r);
        tos.push(reduce_s);
    }
}

// Build the "default_goto" table
fn goto_actions(
    gram: &Grammar,
    nstates: usize,
    gotos: &GotoMap,
    default_goto_table: &[State],
    froms: &mut Vec<Vec<i16>>,
    tos: &mut Vec<Vec<StateOrRule>>,
) {
    let nvars = gotos.num_keys();
    // Reserve area where we will write new entries.
    // We do not write them sequentially, so we reserve space first, then write at indices.
    froms.extend(repeat(Vec::new()).take(nvars));
    tos.extend(repeat(Vec::new()).take(nvars));
    let goto_froms = &mut froms[nstates * 2..];
    let goto_tos = &mut tos[nstates * 2..];

    for var in gram.iter_vars().skip(1) {
        let symbol = gram.var_to_symbol(var);
        let default_state = default_goto_table[var.index()];

        // was: save_column
        let mut spf = Vec::new();
        let mut spt = Vec::new();
        for &entry in gotos.values(var).iter() {
            if entry.to_state != default_state {
                spf.push(entry.from_state.0);
                spt.push(entry.to_state.0);
            }
        }
        let col = gram.value[symbol.index()] as usize;
        goto_froms[col] = spf;
        goto_tos[col] = spt;
    }
}

/// Compute the default goto for a given symbol
/// state_count - a temporary table that can be used by this fn. contents when the function
/// is called are undefined. length  = nstates.
///
/// Returns: Var -> State
fn default_goto_table(nstates: usize, gotos: &GotoMap) -> Vec<State> {
    let mut state_count: Vec<i16> = vec![0; nstates]; // temporary data, used in default_goto()
    gotos
        .iter_entries()
        .map(move |var_gotos| {
            if var_gotos.is_empty() {
                State(0)
            } else {
                fill_copy(&mut state_count, 0);
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
                State(default_state as i16)
            }
        })
        .collect()
}

/// Reads ActionTable.tally and width and produces a sorted index vector over
/// those two parallel vectors. The vector is sorted in descending order of 'width',
/// then descending order of tally.
fn sort_actions(act: &ActionsTable) -> Vec<usize> {
    use std::cmp::Ordering;
    let mut order: Vec<usize> = Vec::with_capacity(act.nvectors);
    for col in 0..act.nvectors {
        let t = act.tally(col);
        if t > 0 {
            order.push(col);
        }
    }
    order.sort_by(|&a, &b| {
        let a = a as usize;
        let b = b as usize;
        match act.width(b).cmp(&act.width(a)) {
            Ordering::Equal => act.tally(b).cmp(&act.tally(a)),
            c => c,
        }
    });
    order
}

mod packing {
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
        // debug!("pack_vector: vector={} lowzero={}", vector, pack.lowzero);
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

            return j as i16;
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

    pub struct PackedTables {
        pub base: Vec<i16>,
        pub table: Vec<i16>,
        pub check: Vec<i16>,
        pub high: usize,
    }

    use super::ActionsTable;
    use log::debug;
    use std::iter::repeat;

    pub fn pack_table(nstates: usize, order: &[usize], act: &ActionsTable) -> PackedTables {
        debug!("pack_table: nentries={}", order.len());

        let initial_maxtable = 1000;

        let mut pack = PackState {
            base: vec![0; act.nvectors],
            pos: vec![0; order.len()],
            table: vec![0; initial_maxtable],
            check: vec![-1; initial_maxtable],
            lowzero: 0,
            high: 0,
            order: order,
            nstates: nstates,
            act: act,
        };

        for i in 0..order.len() {
            let place = match matching_vector(&pack, i) {
                Some(state) => pack.base[state],
                None => pack_vector(&mut pack, i),
            };

            pack.pos[i] = place;
            pack.base[order[i]] = place;
        }

        pack.check.truncate(pack.high + 1);
        pack.table.truncate(pack.high + 1);

        PackedTables {
            base: pack.base,
            table: pack.table,
            check: pack.check,
            high: pack.high,
        }
    }
}
