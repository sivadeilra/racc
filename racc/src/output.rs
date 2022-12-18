use super::*;
use crate::grammar::Grammar;
use crate::lalr::GotoMap;
use crate::mkpar::{ActionCode, YaccParser};
use crate::util::fill_copy;
use crate::{Rule, State, StateOrRule};
use log::debug;
use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use std::cmp;
use std::i16;
use std::iter::repeat;
use syn::{Block, Ident, Type};

/// Given a constructed parser (a description of a state machine which parses a given grammar),
/// produces a TokenStream which implements the parser.
pub(crate) fn output_parser_to_token_stream(
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

    let mut items: TokenStream = TokenStream::new();

    let default_reductions = crate::mkpar::default_reductions(&parser.actions);

    //  Generate YYDEFRED table.
    let yydefred: Vec<i16> = default_reductions
        .iter()
        .map(|&s| if s != Rule(0) { s.0 - 2 } else { 0 })
        .collect();
    items.extend(make_table_i16(
        Ident::new("YYDEFRED", grammar_span),
        &yydefred,
    ));

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
        items.extend(quote!(pub const #tok_ident: u16 = #tokvalue;));
    }

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

        let block_span: Span;
        let stmts: TokenStream = match block {
            Some(block) => {
                // We need to pop items off the stack and associate them with variables from right
                // to left. The bindings are listed in the order that they are declared in, from
                // left to right. The values are stored in 'value_stack' in the same order, with
                // the left-most values being at lower indexes in 'value_stack'.
                //
                // Unfortunately, the most natural way to remove things from a `Vec` is to use
                // `pop()`, which will produce the values in reverse order. To account for this,
                // we reverse the RHS items and use `pop()`. This gives us the order that we want.
                block_span = block.span();
                let rhs_index = gram.rrhs(rule).index();
                let num_rhs = gram.get_rhs_items(rule).len();
                let mut t = TokenStream::new();

                // We insert this assertion check so that the optimizer can eliminate some redundant
                // range checks. If we call Vec::pop() repeatedly, we get one range check (one
                // unwrap call) in the generated code, for each value that we pop. But if we
                // assert that the Vec has enough items, the optimizer is smart enough to see that
                // all of the unwrap() calls can be eliminated. For this reason, the assert has
                // to be a release-mode assert, not just a debug-only assert.
                if num_rhs > 0 {
                    t.extend(quote! {
                        assert!(values.len() >= #num_rhs);
                    });
                }

                for rhs_binding in rhs_bindings[rhs_index..][..num_rhs].iter().rev() {
                    t.extend(match rhs_binding {
                        Some(ref rbind) => {
                            quote! {
                                let mut #rbind = values.pop().unwrap().value;
                            }
                        }
                        None => {
                            // The rule has no binding for this value.  Pop it from the stack and
                            // discard it.
                            quote! {
                                let _ = values.pop();
                            }
                        }
                    })
                }
                t.extend(quote! {#block});
                t
            }
            None => {
                // This reduction does not have any code to execute.  Still, we need to
                // remove items from the value stack. Vec::drain() handles this for us, implicitly.
                block_span = gram.rule_span(Rule(rule_i as i16));
                TokenStream::new()
            }
        };

        let pat_value: u16 = rule_i as u16 - 2;

        action_arms.extend(quote_spanned! {
            block_span =>
            #pat_value => {
                #stmts
            }

        });
    }

    items.extend(quote! {
        #[allow(unused_braces)]
        #[allow(unused_mut)]
        fn reduce_actions(
            mut values: &mut Vec<ValueEntry>,
            reduction: u16,
            #context_param_ident: &mut #context_ty) -> Result<#symbol_value_ty, racc_runtime::Error> {

            Ok(match reduction {
                #action_arms
                _ => unreachable!()
            })
        }
    });

    items.extend(output_rule_data(gram));

    // Emit the YYLEN table.
    items.extend(make_table_i16(
        Ident::new("YYLEN", grammar_span),
        &gram
            .iter_rules()
            .skip(2)
            .map(|r| gram.rule_rhs_syms(r).len() as i16)
            .collect::<Vec<i16>>(),
    ));

    // emit some tables just for debugging
    items.extend(make_symbol_names_table(grammar_span, gram));

    items.extend(make_rule_text_table(grammar_span, gram));

    items.extend(make_states_text_table(grammar_span, gram, parser));

    items.extend(output_gen_methods(symbol_value_ty, context_ty));

    items
}

fn output_gen_methods(symbol_value_ty: Type, context_ty: Type) -> TokenStream {
    quote! {
        /// An active instance of a parser.  This structure contains the state of a parsing state
        /// machine, including the state stack and the value stack.
        ///
        /// To create an instance of `ParserState`, use `ParserState::new`.
        struct ParserState {
            yystate: u16,
            /// Contains (symbol, value), where symbol is either the token that gave us a value,
            /// or a variable that produced a value.
            value_stack: Vec<ValueEntry>,
            state_stack: Vec<u16>,
        }

        struct ValueEntry {
            origin: ValueOrigin,
            value: #symbol_value_ty,
        }

        impl core::fmt::Debug for ValueEntry {
            fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                let mut tuple = fmt.debug_tuple("");

                match &self.origin {
                    &ValueOrigin::Token(t) => {
                        if let Some(name) = YYNAME.get(t as usize) {
                            tuple.field(name);
                        } else {
                            tuple.field(&t);
                        }
                    }
                    &ValueOrigin::Rule(r) => {
                        if let Some(s) = YYRULES.get(r as usize) {
                            tuple.field(&s);
                        } else {
                            tuple.field(&r);
                        }
                    }
                }

                tuple.field(&self.value);
                tuple.finish()
            }
        }

        enum ValueOrigin {
            Token(i16),
            Rule(i16),
        }

        // The initial state for all parsers.
        const INITIAL_STATE: u16 = 0;

        impl Default for ParserState {
            fn default() -> ParserState {
                ParserState {
                    yystate: INITIAL_STATE,
                    value_stack: Vec::new(),
                    state_stack: {
                        let mut v = Vec::with_capacity(20);
                        // v.push(INITIAL_STATE);
                        v
                    },
                }
            }
        }

        impl ParserState {
            /// Initializes a new `ParserState`, given the parsing tables that were generated by the
            /// `grammar!` macro.  Use the `push_token` and `finish` methods to advance the state of
            ///  the parser.  Use the `reset` method to reset the parser to its initial state.
            pub fn new() -> Self {
                Self::default()
            }

            /// Resets this parser to its initial state, exactly as if `Parser::new` had been used
            /// to generate a new ParserState object.  There is no semantic difference between using
            /// `Parser::new` and using `reset()`.  The `reset()` parser may be more efficient,
            /// since it does not require freeing and reallocating the internal state tables.
            pub fn reset(&mut self) {
                self.yystate = INITIAL_STATE;
                self.value_stack.clear();
                self.state_stack.clear();
                // self.state_stack.push(INITIAL_STATE);
            }

            // Do default reductions, as long as there are any default reductions.
            // Returns true if we performed at least one default reduction.
            fn do_defreds(&mut self, ctx: &mut #context_ty) -> Result<(), racc_runtime::Error> {
                // Check for default reductions.
                loop {
                    // Keep in mind that the values in YYDEFRED are biased by 2, in order to save
                    // space in related tables.
                    let defred = YYDEFRED[self.yystate as usize];
                    if defred != 0 {
                        log::debug!("do_defreds: s{} has default reduction r{}", self.yystate, defred + 2);
                        self.yyreduce(defred, ctx)?;
                    } else {
                        return Ok(());
                    }
                }
            }

            // Check to see if there is a REDUCE action for this (state, token).
            fn try_reduce(&mut self, ctx: &mut #context_ty, token: u16)
                -> Result<bool, racc_runtime::Error>
            {
                let red = YYRINDEX[self.yystate as usize];
                if red == 0 {
                    log::debug!("try_reduce: s{} has no reductions", self.yystate);
                    return Ok(false);
                }

                let yyn = red + (token as u16);
                if YYCHECK[yyn as usize] != token as i16 {
                    log::debug!("try_reduce: s{} has no reduction for token {}", self.yystate, YYNAME[token as usize]);
                    return Ok(false);
                }

                let rr = YYTABLE[yyn as usize] as u16;
                self.yyreduce(rr, ctx)?;
                Ok(true)
            }

            // Performs a reduction.
            fn yyreduce(&mut self, reduction: u16, ctx: &mut #context_ty)
                -> Result<(), racc_runtime::Error>
            {
                let len = YYLEN[reduction as usize] as usize;
                let lhs = YYLHS[reduction as usize];

                log::debug!(
                    "yyreduce: reducing: r{} (lhs {}, len {}) {}",
                    reduction + 2, lhs, len, YYRULES[reduction as usize]
                );
                assert!(self.value_stack.len() >= len);
                // assert!(self.state_stack.len() >= len, "state stack is too small. needed {}, stack has {}", len, self.state_stack.len());

                // Invoke the generated "reduce" method.  This method handles popping values from
                // parser.values_stack, and then executing the app-supplied code for this reduction.
                // Because the generated code handles popping items from the stack, it is not
                // necessary for us to consult a 'yylen' table here; that information is implicit.
                let old_values_len = self.value_stack.len();
                let reduce_value = reduce_actions(
                    &mut self.value_stack,
                    reduction,
                    ctx)?;
                assert!(self.value_stack.len() + len == old_values_len);
                log::trace!(
                    "yyreduce: generated code popped {} values from value stack, new len = {}",
                    len,
                    self.value_stack.len()
                );

                // Push the value that represents the reduction of this rule (the LHS).
                log::debug!("yyreduce: action produced value: {:?}", reduce_value);
                self.value_stack.push(ValueEntry {
                    origin: ValueOrigin::Rule(reduction as i16),
                    value: reduce_value,
                });

                // Pop states. The number of states that we pop is equal to the number of symbols
                // on the RHS of the current rule (which can be zero).  We treat yystate as one of
                // the entries to be popped. This is why we pop `len - 1` items from the actual
                // stack.  Then, if the stack is empty, we set the current state to zero (the
                // initial state value).
                if len > 0 {
                    for _ in 0..len - 1 {
                        let discard_state = self.state_stack.pop().unwrap();
                        log::debug!("yyreduce: popped state: s{} (discarded)", discard_state);
                    }
                    self.yystate = if let Some(s) = self.state_stack.pop() {
                        log::debug!("yyreduce: popped state: s{}", s);
                        s
                    } else {
                        log::debug!("yyreduce: stack is empty, using s0");
                        0
                    };
                } else {
                    log::debug!("yyreduce: rule has no rhs symbols (epsilon rule)");
                }

                log::debug!("states: {:?} {}", self.state_stack, self.yystate);

                if self.yystate == 0 && lhs == 0 {
                    log::debug!(
                        "yyreduce: after reduction, shifting to state {} (0/0 case!)",
                        YYFINAL
                    );
                    self.yystate = YYFINAL;
                    // self.state_stack.push(YYFINAL);

                    // todo: port acceptance code
                } else {
                    let yyn_0 = YYGINDEX[lhs as usize] as u16;

                    let next_state: u16 = if yyn_0 != 0 {
                        let yyn_1 = yyn_0 + self.yystate;
                        if YYCHECK[yyn_1 as usize] as u16 == self.yystate {
                            let s = YYTABLE[yyn_1 as usize] as u16;
                            log::debug!("yyreduce: yycheck passes, yytable[{}] = s{}", yyn_1, s);
                            s
                        } else {
                            let s = YYDGOTO[lhs as usize] as u16;
                            log::debug!("yyreduce: yycheck fails, yydgoto[{}] = s{}", lhs, s);
                            s
                        }
                    } else {
                        let s = YYDGOTO[lhs as usize] as u16;
                        log::debug!("yyreduce: yygindex[] is zero, yydgoto[{}] = s{}", lhs, s);
                        s
                    };

                    self.state_stack.push(self.yystate);
                    self.yystate = next_state;

                    log::debug!("states: {:?} {}", self.state_stack, self.yystate);
                }

                Ok(())
            }

            // Check to see if there is a SHIFT action for this (state, token).
            // All of the values in YYSINDEX are either 0 (meaning no shift) or negative.
            // If YYSINDEX[state] is non-zero, then (token + YYSINDEX[state]) gives yyn.
            fn try_shift(&mut self, token: u16, lval: #symbol_value_ty) -> bool {
                let shift: i16 = YYSINDEX[self.yystate as usize];
                if shift == 0 {
                    // log::debug!("try_shift: no shift");
                    return false;
                }

                let yyn_i32 = shift as i32 + (token as i32);
                assert!(yyn_i32 >= 0);
                let yyn = yyn_i32 as usize;

                if YYCHECK[yyn] as u16 != token {
                    // log::debug!("try_shift: no shift (yycheck failed)");
                    return false;
                }

                let next_state = YYTABLE[yyn] as u16;

                self.state_stack.push(self.yystate);
                self.yystate = next_state;
                log::debug!("states: {:?} {}", self.state_stack, self.yystate);

                // log::debug!("try_shift: shifted state: {:?} {}", self.state_stack, self.yystate);

                log::debug!("try_shift: pushed value: {:?}", lval);
                self.value_stack.push(ValueEntry {
                    origin: ValueOrigin::Token(token as i16),
                    value: lval, // <-- lval is moved
                });
                true
            }

            /// Parses an input stream of tokens and returns the result value.
            ///
            /// This provides an interface that is similar to the `yyparse()` function generated by
            /// YACC. It handles creating a parser, pushing tokens into it, and getting the final
            /// value that was produced by the parser.
            #[allow(dead_code)]
            pub fn parse<TI>(tokens: TI, ctx: &mut #context_ty) -> Result<#symbol_value_ty, racc_runtime::Error>
            where
                TI: Iterator<Item = (u16, #symbol_value_ty)>
            {
                let mut parser = Self::default();

                for (token, lval) in tokens {
                    parser.push_token(ctx, token, lval)?;
                }

                parser.finish(ctx)
            }

            /// Advances the state of the parser by reporting a new token to the parser.
            ///
            /// Calling this method is the equivalent of returning a token (other than `YYEOF`)
            /// from a `yylex()` function in a YACC parser.
            pub fn push_token(
                &mut self,
                ctx: &mut #context_ty,
                token: u16,
                lval: #symbol_value_ty,
            ) -> Result<(), racc_runtime::Error> {
                log::debug!(
                    "------------- push_token: reading {} ({}) lval {:?} -------------",
                    token, YYNAME[token as usize], lval
                );
                // log::debug!("state: s{} {}", self.yystate, YYSTATE_TEXT[self.yystate as usize]);
                log::debug!("states: {:?} {}", self.state_stack, self.yystate);
                log::debug!("values: {:?}", self.value_stack);

                let mut any_reduce = false;

                loop {
                    if self.try_shift(token, lval) {
                        self.do_defreds(ctx)?;
                        break;
                    } else {
                        while self.try_reduce(ctx, token)? {
                            any_reduce = true;
                            self.do_defreds(ctx)?;
                        }

                        if !any_reduce {
                            // If there is neither a shift nor a reduce action defined for this (state, token),
                            // then we have encountered a syntax error.
                            log::debug!("syntax error!  token is not recognized in this state.");
                            return Err(racc_runtime::Error::SyntaxError);
                        }
                    }
                }

                log::debug!("states: {:?} {}", self.state_stack, self.yystate);
                log::debug!("values: {:?}", self.value_stack);
                Ok(())
            }

            /// Pushes the final "end of input" token into the state machine, and checks whether the
            /// grammar has accepted or rejected the sequence of tokens.
            ///
            /// Calling this method is the equivalent of returning `YYEOF` from a `yylex()` function
            /// in a YACC parser.
            pub fn finish(&mut self, ctx: &mut #context_ty)
                -> Result<#symbol_value_ty, racc_runtime::Error>
            {
                // assert!(!self.state_stack.is_empty());

                log::debug!("------------- finish -------------");
                log::debug!("states: {:?} {}", self.state_stack, self.yystate);
                log::debug!("values: {:?}", self.value_stack);

                let mut any_reduce = false;

                loop {
                    if self.try_reduce(ctx, 0)? {
                        self.do_defreds(ctx)?;
                        any_reduce = true;
                    } else {
                        break;
                    }
                }

                self.do_defreds(ctx)?;

                if self.value_stack.len() == 1 {
                    log::debug!("accept");
                    let final_lval = self.value_stack.pop().unwrap();
                    return Ok(final_lval.value);
                }

                log::debug!(
                    "done with all reductions.  yystate={:?}  state_stack={:?}",
                    self.yystate, self.state_stack
                );

                // If there is neither a shift nor a reduce action defined for this (state, token),
                // then we have encountered a syntax error.

                log::debug!("syntax error!  token is not recognized in this state.");
                log::debug!("values: {:?}", self.value_stack);
                Err(racc_runtime::Error::SyntaxError)
            }
        }
    }
}

// Generates the YYLHS table.
fn output_rule_data(gram: &Grammar) -> TokenStream {
    let mut data: Vec<i16> = Vec::new();
    data.push(gram.value[gram.start().index()]);
    for i in 3..gram.nrules {
        data.push(gram.value[gram.rlhs[i].0 as usize]);
    }
    make_table_i16_signed(Ident::new("YYLHS", Span::call_site()), &data)
}

fn make_symbol_names_table(span: Span, gram: &Grammar) -> TokenStream {
    // The values used at runtime are not symbol indices.  They are token values, which come from
    // gram.value[token].value. This is ugly and inefficient.

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

fn make_states_text_table(span: Span, gram: &Grammar, parser: &YaccParser) -> TokenStream {
    let ss: Vec<String> = parser
        .actions
        .iter()
        .enumerate()
        .map(|(state, actions)| {
            use std::fmt::Write;
            let mut s = String::new();
            for action in actions.iter() {
                write!(
                    s,
                    "s{} : {} -> ",
                    state,
                    gram.name(action.symbol.to_symbol())
                )
                .unwrap();
                match action.action_code {
                    ActionCode::Shift(to_state) => {
                        writeln!(s, "shift to s{}", to_state).unwrap();
                    }
                    ActionCode::Reduce(rule) => {
                        writeln!(s, "reduce {}", gram.rule_to_str(rule)).unwrap();
                    }
                }
            }
            s
        })
        .collect::<Vec<String>>();
    make_table_string(Ident::new("YYSTATE_TEXT", span), &ss)
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
        default_reductions,
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
    let order = sort_actions(&act);
    let packed = packing::pack_table(parser.nstates(), &order, &act);

    let mut items = TokenStream::new();

    // The YYDGOTO table contains a mapping from variables to states. However, the table does
    // not include an entry for the 'start' symbol, so the length of YYDGOTO is `nvars - 1`, not
    // `nvars`. See `goto_actions` in the C code. This is why we call skip(1), below.
    items.extend(make_table_i16_signed(
        Ident::new("YYDGOTO", span),
        &default_goto_table
            .iter()
            .skip(1)
            .map(|s| s.0)
            .collect::<Vec<i16>>(),
    ));

    items.extend(make_table_i16_signed(
        Ident::new("YYSINDEX", span),
        &packed.base[..nstates],
    ));
    items.extend(make_table_i16(
        Ident::new("YYRINDEX", span),
        &packed.base[nstates..nstates * 2],
    ));
    items.extend(make_table_i16_signed(
        Ident::new("YYGINDEX", span),
        &packed.base[nstates * 2..act.nvectors - 1],
    ));
    items.extend(make_table_i16_signed(
        Ident::new("YYTABLE", span),
        &packed.table,
    ));
    items.extend(make_table_i16_signed(
        Ident::new("YYCHECK", span),
        &packed.check,
    ));
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
            froms: Vec::new(),
            tos: Vec::new(),
        }
    }
    pub fn tally(&self, i: usize) -> usize {
        self.froms[i].len()
    }
    pub fn width(&self, i: usize) -> i16 {
        let f = &self.froms[i];
        if !f.is_empty() {
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
    for actions in parser.actions.iter() {
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
    for (state, actions) in parser.actions.iter().enumerate() {
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

/// Build the "default_goto" table
fn goto_actions(
    gram: &Grammar,
    nstates: usize,
    gotos: &GotoMap,
    default_goto_table: &[State],
    froms: &mut Vec<Vec<i16>>,
    tos: &mut Vec<Vec<StateOrRule>>,
) {
    debug!("goto_actions:");
    let nvars = gotos.len();
    assert_eq!(nvars, gram.nvars);
    // Reserve area where we will write new entries.
    // We do not write them sequentially, so we reserve space first, then write at indices.
    froms.extend(repeat(Vec::new()).take(nvars));
    tos.extend(repeat(Vec::new()).take(nvars));
    let goto_froms = &mut froms[nstates * 2..];
    let goto_tos = &mut tos[nstates * 2..];
    for var in gram.iter_vars() {
        if var.index() == 0 {
            continue;
        }
        let symbol = gram.var_to_symbol(var);
        let default_state = default_goto_table[var.index()];
        let mut spf = Vec::new();
        let mut spt = Vec::new();
        for &entry in &gotos[var.index()] {
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
        .iter()
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
    order.sort_by(|&a, &b| match act.width(b).cmp(&act.width(a)) {
        Ordering::Equal => act.tally(b).cmp(&act.tally(a)),
        c => c,
    });
    order
}

mod packing {
    use super::ActionsTable;
    use log::debug;

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

    pub struct PackedTables {
        pub base: Vec<i16>,
        pub table: Vec<i16>,
        pub check: Vec<i16>,
        pub high: usize,
    }

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
            high: pack.high,
        }
    }
}
