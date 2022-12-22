use super::*;
use crate::lalr::LALROutput;
use crate::util::fill_copy;
use crate::{Rule, State, StateOrRule};
use log::debug;
use std::cmp;
use std::iter::repeat;
use syn::{Ident, Type};

fn output_parser_struct(needs_token_stack: bool) -> syn::Item {
    let token_stack_field = if needs_token_stack {
        quote!(token_stack: Vec<Token>,)
    } else {
        quote!(token_stack: (),)
    };

    parse_quote! {
        /// Parses the grammar that you have defined.
        ///
        /// This structure contains the state of a parsing state machine, including the state stack
        /// and the value stack. If your grammar returns values from rules, then this parser
        /// may hold instances of those values.
        pub struct Parser {
            yystate: u16,
            /// Contains (symbol, value), where symbol is either the token that gave us a value,
            /// or a variable that produced a value.
            value_stack: Vec<VarValue>,
            #token_stack_field // token_stack: Vec<Token>,
            state_stack: Vec<u16>,
        }
    }
}

pub(crate) fn output_parser(
    gram: &Grammar,
    _lr0: &LR0Output,
    _lalr: &LALROutput,
    default_reductions: &[Rule],
    default_goto_table: &[State],
    parser: &YaccParser,
    packed: &PackedTables,
) -> TokenStream {
    let mut errors = Errors::default();

    // Scan the tokens to see whether none/some/all carry values.
    // We use this to decide whether to emit a token stack or not.

    let mut any_token_has_value = false;
    let mut any_token_no_value = false;

    for t in 1..gram.ntokens {
        if gram.sym_type[t].is_some() {
            any_token_has_value = true;
        } else {
            any_token_no_value = true;
        }
    }
    let needs_token_stack = any_token_has_value;

    let mut output_mod: syn::ItemMod = parse_quote! {
        mod this_name_is_not_used {

            use racc_runtime::racc_log;

            // The initial state for all parsers.
            const INITIAL_STATE: u16 = 0;

            impl Default for Parser {
                fn default() -> Parser {
                    Parser {
                        yystate: INITIAL_STATE,
                        value_stack: Vec::new(),
                        token_stack: Default::default(),
                        state_stack: Vec::with_capacity(20),
                    }
                }
            }

        }
    };

    let items: &mut Vec<syn::Item> = &mut output_mod.content.as_mut().unwrap().1;

    items.push(output_parser_struct(needs_token_stack));

    // Create fragments for passing context through.
    let context_param: TokenStream;
    let context_arg: TokenStream;
    if let Some(context_ty) = &gram.context_ty {
        context_param = quote!(context: &mut #context_ty,);
        context_arg = quote!(context,);
    } else {
        context_param = quote!();
        context_arg = quote!();
    }

    // The YYDGOTO table contains a mapping from variables to states. However, the table does
    // not include an entry for the 'start' symbol, so the length of YYDGOTO is `nvars - 1`, not
    // `nvars`. See `goto_actions` in the C code. This is why we call skip(1), below.
    let yydgoto_table: Vec<i16> = default_goto_table
        .iter()
        .skip(1)
        .map(|s| s.0)
        .collect::<Vec<i16>>();
    items.push(make_table_i16_signed(
        Ident::new("YYDGOTO_UNUSED", Span::call_site()),
        &yydgoto_table,
    ));

    items.push(make_table_i16_signed(
        Ident::new("YYSINDEX", Span::call_site()),
        &packed.sindex_table(),
    ));
    items.push(make_table_i16_signed(
        Ident::new("YYRINDEX", Span::call_site()),
        packed.rindex_table(),
    ));

    // TODO: Can we stop encoding YYGINDEX in the packed table now?
    let yygindex_table = packed.gindex_table();
    if false {
        items.push(make_table_i16_signed(
            Ident::new("YYGINDEX", Span::call_site()),
            yygindex_table,
        ));
    }
    items.push(make_table_i16_signed(
        Ident::new("YYTABLE", Span::call_site()),
        &packed.table,
    ));
    items.push(make_table_i16_signed(
        Ident::new("YYCHECK", Span::call_site()),
        &packed.check,
    ));

    // Generate YYFINAL constant.
    let yyfinal = parser.final_state.0 as u16;

    let fake_mod: syn::ItemMod = parse_quote! {
        mod name_is_not_used {
            const YYFINAL: u16 = #yyfinal;

            #[inline(never)]
            #[cold]
            fn error_invalid_token_in_token_stack(t: Token) -> ! {
                panic!("unexpected token in token stack: {:?}", t);
            }

            #[inline(never)]
            #[cold]
            fn error_invalid_value_in_values_stack(v: VarValue) -> ! {
                panic!("unexpected value in value stack: {:?}", v);
            }

            #[inline(never)]
            #[cold]
            fn yyreduce_value_stack_check_panic(actual: usize, needed: usize) -> ! {
                panic!("value stack was expected to contain at least {} values, but only contains {} values", needed, actual);
            }

            #[inline(never)]
            #[cold]
            fn yyreduce_token_stack_check_panic(actual: usize, needed: usize) -> ! {
                panic!("token stack was expected to contain at least {} tokens, but only contains {} tokens", needed, actual);
            }
        }
    };
    items.extend(fake_mod.content.unwrap().1);

    items.push(output_rule_data(gram));

    // Emit the YYLEN table.
    if false {
        // We no longer need this, but it might be good to emit this for diagnostics.
        items.push(make_table_i16(
            Ident::new("YYLEN", Span::call_site()),
            &gram
                .iter_rules()
                .skip(2)
                .map(|r| gram.rule_rhs_syms(r).len() as i16)
                .collect::<Vec<i16>>(),
        ));
    }

    // emit some tables just for debugging
    items.push(make_symbol_names_table(Span::call_site(), gram));
    items.push(make_rule_text_table(Span::call_site(), gram));
    items.push(make_states_text_table(Span::call_site(), gram, parser));

    // Things that go inside the `impl Parser` block.

    let mut parser_impl: syn::ItemImpl = parse_quote! {
        impl Parser {
            /// Initializes a new `Parser`, given the parsing tables that were generated by the
            /// `grammar!` macro.  Use the `push` and `finish` methods to advance the state of
            ///  the parser.  Use the `reset` method to reset the parser to its initial state.
            pub fn new() -> Self {
                Self::default()
            }

            /// Resets this parser to its initial state, exactly as if `Parser::new` had been used
            /// to generate a new Parser object.  There is no semantic difference between using
            /// `Parser::new` and using `reset()`.  The `reset()` parser may be more efficient,
            /// since it does not require freeing and reallocating the internal state tables.
            pub fn reset(&mut self) {
                self.yystate = INITIAL_STATE;
                self.value_stack.clear();
                self.token_stack = Default::default();
                self.state_stack.clear();
            }

            // Check to see if there is a REDUCE action for this (state, token).
            fn try_reduce(&mut self, #context_param token: i16)
                -> Result<bool, racc_runtime::Error>
            {
                assert_eq!(YYTABLE.len(), YYCHECK.len());

                let red = YYRINDEX[self.yystate as usize];
                if red == 0 {
                    racc_log!("try_reduce: s{} has no reductions", self.yystate);
                    return Ok(false);
                }

                let yyn = red as i32 + token as i32;
                racc_log!("try_reduce: red = {}, yyn = {}", red, yyn);
                if yyn < 0 || yyn as usize >= YYCHECK.len() || YYCHECK[yyn as usize] != token {
                    racc_log!("try_reduce: s{} has no reduction for token {}", self.yystate, YYNAME[token as usize]);
                    return Ok(false);
                }

                let rr = YYTABLE[yyn as usize] as u16;
                self.yyreduce(rr, #context_arg)?;

                self.do_default_reductions(#context_arg)?;

                Ok(true)
            }
        }
    };

    let parser_methods = &mut parser_impl.items;

    parser_methods.push(output_push(
        gram,
        needs_token_stack,
        any_token_no_value,
        &context_param,
        &context_arg,
    ));

    // Determine the return type for the finish() and parse() methods.
    let top_sym = gram.goal();
    let return_ty: Option<&syn::Type> = gram.sym_type[top_sym.index()].as_ref();
    let return_ty_tokens = if let Some(rt) = return_ty {
        rt.to_token_stream()
    } else {
        quote!(())
    };

    parser_methods.push(output_finish(
        gram,
        &context_param,
        &context_arg,
        needs_token_stack,
    ));

    parser_methods.push(output_parse(
        &context_param,
        &context_arg,
        &return_ty_tokens,
    ));

    parser_methods.push(errors.combine_with(output_yyreduce(
        gram,
        yygindex_table,
        &yydgoto_table,
        &context_param,
        &context_arg,
    )));

    items.push(output_default_reductions_table(&default_reductions));

    parser_methods.push(output_do_default_reductions(&context_param, &context_arg));

    items.push(syn::Item::Impl(parser_impl));

    items.push(output_token_to_i16(gram));
    items.push(output_token_enum(gram));
    items.push(output_var_value_enum(gram));

    // We only need the token_has_value() function is there are both tokens
    // that have a value and tokens that don't.
    if any_token_has_value && any_token_no_value {
        items.push(output_token_has_value(gram));
    }

    let output_tokens: TokenStream = output_mod
        .content
        .unwrap()
        .1
        .into_iter()
        .map(|item| item.into_token_stream())
        .collect();

    errors.into_token_stream_and_combine(output_tokens)
}

macro_rules! extend_stmt_parse_quote_spanned {
    (
        $stmts:expr,
        $span:expr =>
        $($t:tt)*
    ) => {
        {
            let b: syn::Block = parse_quote_spanned!($span => { $($t)* });
            $stmts.extend(b.stmts);
        }
    }
}

fn output_yyreduce(
    gram: &Grammar,
    yygindex_table: &[i16],
    yydgoto_table: &[i16],
    context_param: &TokenStream,
    context_arg: &TokenStream,
) -> WithErrors<syn::ImplItem> {
    // Build up actions for reductions. Each action handles popping token values and variable
    // values off the corresponding stacks (token_stack and value_stack), executing "action" code
    // that was provided in the grammar definition, and then pushing the resulting value onto
    // value_stack.
    //
    // We only pop and push values for tokens and variables that actually have a value. For tokens
    // and variables that do not have a value, we don't need to push or pop anything, because all
    // of the information that we need is encoded in the state number.

    let mut errors = Errors::default();

    let mut reduction_match: syn::ExprMatch = parse_quote! {
        match reduction {
            0u16 => {
                // This is the rule for $accept : Goal EOF.
                // We never actually call yyreduce for this rule.
                unreachable!();
            }
        }
    };

    let mut all_action_funcs = TokenStream::new();

    for (rule_i, block) in gram.rule_blocks.iter().enumerate() {
        // We process all rules defined by the grammar, but ignore the 3 predefined rules.
        if rule_i < 3 {
            continue;
        }

        let rule = Rule(rule_i as i16);

        // This is the value used in the match statement. It uses the +2 bias.
        let pat_value: u16 = rule_i as u16 - 2;

        let mut stmts0 = TokenStream::new();
        let mut stmts1: Vec<syn::Stmt> = Vec::new();

        // Based on the rule we are reducing, get values from the value stack,
        // and bind them as a tuple named 'args'.

        let rhs_index = gram.rrhs(rule).index();
        let num_rhs = gram.get_rhs_items(rule).len();
        let rhs_syms = gram.rule_rhs_syms(rule);
        let rhs_bindings = &gram.rhs_binding[rhs_index..][..num_rhs];
        let rule_span = gram.rule_span(rule);

        // Look up the LHS of the rule. Find the value type for that variable.
        let lhs = gram.rlhs(rule);
        let lhs_ident = gram.name(lhs);
        let lhs_sym_type_opt = gram.sym_type[lhs.index()].as_ref();

        // Iterate the rhs symbols and generate code that pops the values for each rhs
        // symbol from the stack. If the value is used by the rule, then verify that it
        // has the expected type.

        let mut num_value_stack_pop: usize = 0;
        let mut num_token_stack_pop: usize = 0;

        let mut action_func_params = TokenStream::new();
        let mut action_func_call_args = TokenStream::new();

        for (rhs_sym_or_rule, rhs_binding) in rhs_syms.iter().rev().zip(rhs_bindings.iter().rev()) {
            assert!(rhs_sym_or_rule.is_symbol());
            let rhs_sym = rhs_sym_or_rule.as_symbol();
            let rhs_ident = gram.name(rhs_sym);
            let rhs_sym_ty_opt = gram.sym_type[rhs_sym.index()].as_ref();

            if let Some(rbind) = rhs_binding {
                if let Some(rhs_sym_ty) = rhs_sym_ty_opt {
                    // Is the symbol a token or a value produced by a rule?
                    if gram.is_var(rhs_sym) {
                        // The rhs symbol is a var. Verify that the item popped from the
                        // stack has the right type (right enum variant). As long as
                        // the grammar tables are correctly constructed, this should
                        // always be true.
                        num_value_stack_pop += 1;

                        if gram.nvars == 2 {
                            // Some grammars have only a single non-terminal.
                            // If we emit the usual `match ...` statement, then the "unrecognized"
                            // arm is provably unreachable. We could generate the "match" and
                            // then suppress the unreachable warning on the default arm, of course.
                            extend_stmt_parse_quote_spanned! {
                                stmts1, rule_span =>
                                let VarValue::#rhs_ident(#rbind) = self.value_stack.pop().unwrap();
                            }
                        } else {
                            extend_stmt_parse_quote_spanned! {
                                stmts1, rule_span =>
                                let #rbind: #rhs_sym_ty = match self.value_stack.pop().unwrap() {
                                    VarValue::#rhs_ident(rhs_value) => rhs_value,
                                    unrecognized => error_invalid_value_in_values_stack(unrecognized),
                                };
                            }
                        }

                        let log_msg = format!(
                            "popped value {}({}) = {{:?}}",
                            rhs_ident.to_string(),
                            rbind.to_string()
                        );
                        stmts1.push(parse_quote_spanned! {
                            rule_span =>
                            racc_log!(#log_msg, #rbind);
                        });
                    } else {
                        // The rhs symbol is a token. Verify that we were given the
                        // right kind of token.
                        num_token_stack_pop += 1;
                        let log_msg = format!(
                            "popped token {}({}) = {{:?}}",
                            rhs_ident.to_string(),
                            rbind.to_string()
                        );
                        extend_stmt_parse_quote_spanned! {
                            stmts1,
                            rule_span =>
                            let #rbind: #rhs_sym_ty = match self.token_stack.pop().unwrap() {
                                Token::#rhs_ident(rhs_value) => rhs_value,
                                unrecognized => error_invalid_token_in_token_stack(unrecognized),
                            };
                            racc_log!(#log_msg, #rbind);
                        }
                    }
                    action_func_params.extend(quote!(mut #rbind: #rhs_sym_ty,));
                    action_func_call_args.extend(quote!(#rbind,));
                } else {
                    // This is not good. The grammar has a binding for this value, but the symbol
                    // that the value should come from does not have a type. This is a grammar
                    // definition error.
                    errors.push(syn::Error::new(
                        rhs_binding.span(),
                        format!(
                            "the symbol '{}' does not have a type specified",
                            gram.name[rhs_sym.index()]
                        ),
                    ));
                }
            } else {
                // The rule has no binding for this value.  Pop it from the stack and
                // discard it.
                if gram.is_var(rhs_sym) {
                    if rhs_sym_ty_opt.is_some() {
                        num_value_stack_pop += 1;
                        let log_msg = format!("popped value {}: {{:?}}", rhs_ident.to_string());
                        stmts1.push(parse_quote_spanned! {
                            rule_span =>
                            let _unused_value = self.value_stack.pop();
                        });
                        stmts1.push(parse_quote_spanned! {
                            rule_span =>
                            racc_log!(#log_msg, _unused_value);
                        });
                    } else {
                        // This variable does not have a value.
                    }
                } else {
                    if rhs_sym_ty_opt.is_some() {
                        num_token_stack_pop += 1;
                        let log_msg = format!("popped token {}: {{:?}}", rhs_ident.to_string());
                        stmts1.push(parse_quote_spanned! {
                            rule_span =>
                            let _unused_token = self.token_stack.pop();
                        });
                        stmts1.push(parse_quote_spanned! {
                            rule_span =>
                            racc_log!(#log_msg, _unused_token);
                        });
                    } else {
                        // For tokens that do not have values, we never even push them on the stack,
                        // so there is no need to pop them.
                    }
                }
            }
        }

        // Now that we know how many items we pop from the value_stack and token_stack, we can
        // insert assertion checks so that the optimizer can eliminate some redundant range checks.
        // If we call Vec::pop() repeatedly, we get one range check (one unwrap call) in the
        // generated code, for each value that we pop. But if we assert that the Vec has enough
        // items, the optimizer is smart enough to see that all of the unwrap() calls can be
        // eliminated. For this reason, the assert has to be a release-mode assert, not a
        // debug_assert!().
        //
        // We insert these assertions into stmts0 so that they precede the pop() calls.

        if num_value_stack_pop > 0 {
            stmts0.extend(quote_spanned! {
                rule_span =>
                // assert!(self.value_stack.len() >= #num_value_stack_pop);
                if self.value_stack.len() < #num_value_stack_pop {
                    yyreduce_value_stack_check_panic(self.value_stack.len(), #num_value_stack_pop);
                }
            });
        }
        if num_token_stack_pop > 0 {
            stmts0.extend(quote_spanned! {
                rule_span =>
                // assert!(self.token_stack.len() >= #num_token_stack_pop);
                if self.token_stack.len() < #num_token_stack_pop {
                    yyreduce_token_stack_check_panic(self.token_stack.len(), #num_token_stack_pop);
                }
            });
        }

        // Insert the action code, supplied by the grammar, if the grammar provided an action.
        // We wrap the action in a separate function, even though that function will only be called
        // once, so that action blocks can safely use "return".
        //
        // If we built a single function which directly contained all of the action blocks, then any
        // action block that used "return" would silently break the state machine, because the work
        // done after the action would be skipped. That work updates the state stack, token stack,
        // etc., so the parser would be in a completely broken state if this code is skipped.
        //
        // The inliner folds the action functions into yyreduce(), so there is no perf cost.

        match block {
            Some(block) => {
                let block_span = block.span();

                // Make a name for the action function. It would suffice to use the action index
                // but that makes debugging difficult, so we append the name of the LHS symbol.
                // We also flatten it to lowercase, to meet Rust's naming convention requirements.
                let rule_func_id = Ident::new(
                    &format!(
                        "action_{}_{}",
                        pat_value,
                        lhs_ident.to_string().to_ascii_lowercase()
                    ),
                    rule_span,
                );

                // Choose the return type for the action function. This will be wrapped in a Result.
                let action_return_ty = if let Some(t) = lhs_sym_type_opt {
                    quote!(#t)
                } else {
                    quote!(())
                };

                // We need to pop items off the stack and associate them with variables from right
                // to left. The bindings are listed in the order that they are declared in, from
                // left to right. The values are stored in 'value_stack' in the same order, with
                // the left-most values being at lower indexes in 'value_stack'.
                //
                // Unfortunately, the most natural way to remove things from a `Vec` is to use
                // `pop()`, which will produce the values in reverse order. To account for this,
                // we reverse the RHS items and use `pop()`. This gives us the order that we want.
                if let Some(sym_type) = lhs_sym_type_opt {
                    extend_stmt_parse_quote_spanned! {
                        stmts1, rule_span =>
                        let rule_output: #sym_type = #rule_func_id(#context_arg #action_func_call_args)?;
                        racc_log!("action produced: {:?}", rule_output);
                        self.value_stack.push(VarValue::#lhs_ident(rule_output));
                    };
                } else {
                    // This rule does not produce a value, so we do not push a value onto value_stack.
                    extend_stmt_parse_quote_spanned! {
                        stmts1, rule_span =>
                        #rule_func_id(#context_arg #action_func_call_args)?;
                    };
                }

                all_action_funcs.extend(quote_spanned! {
                    block_span =>
                    #[inline(always)]
                    #[allow(unused_mut)]
                    fn #rule_func_id(#context_param #action_func_params) -> Result<#action_return_ty, racc_runtime::Error> {
                        Ok(#block)
                    }
                });
            }

            None => {
                // This reduction does not have any code to execute.  We still need to remove values
                // from the stack, but this has already been done, above. We do need to provide a
                // value for this rule, though.
                // TODO: Move this code to the reader phase, and ignore it here.
                if lhs_sym_type_opt.is_some() {
                    // TODO: We could implement a rule where if a rule returns a value, and has
                    // exactly one RHS symbol that returns a value, and the rule has no block, then
                    // we use the RHS value for the return value. That would simplify the common
                    // scenario of: Expr : LITERAL=value { value }.
                    errors.push(syn::Error::new(
                        rule_span,
                        "the result of this rule is required to provide a value; \
                         please provide a { ... } block which computes that value.",
                    ));
                } else {
                    // This rule does not produce a value, so we do not push a value onto value_stack.
                }
            }
        }

        // Now that the tokens/values have been popped, the action block (if any) has run, and the
        // output value has been pushed, we need to update the state stack and yystate. In the
        // original C code, this was driven by a table lookup. However, some of that information
        // is easy to compute during parser generation.

        // Update the state stack. We pop one state for every RHS symbol that we just reduced.
        // It's slightly complicated by the fact that we do not store yystate on the top of the
        // stack. So we special-case things with -1.
        //
        // Pop states. The number of states that we pop is equal to the number of symbols
        // on the RHS of the current rule (which can be zero).  We treat yystate as one of
        // the entries to be popped. This is why we pop `len - 1` items from the actual
        // stack.  Then, if the stack is empty, we set the current state to zero (the
        // initial state value).

        if num_rhs > 0 {
            let num_discard = num_rhs - 1;
            if num_discard > 0 {
                extend_stmt_parse_quote_spanned! {
                    stmts1, rule_span =>
                    // Discard yylen - 1 states from the state stack.
                    self.state_stack.truncate(self.state_stack.len() - #num_discard);
                };
            }

            extend_stmt_parse_quote_spanned! {
                stmts1, rule_span =>
                self.yystate = if let Some(s) = self.state_stack.pop() {
                    racc_log!("yyreduce: popped state: s{}", s);
                    s
                } else {
                    // TODO: Is this right?
                    racc_log!("yyreduce: stack is empty, using s0");
                    0
                };
            }
        } else {
            // This is an empty (epsilon) production. No need to adjust state_stack.
        }

        // yylhs is the symbol value, not our internal index for the symbol
        let yylhs = gram.value[lhs.index()];

        let yygindex = yygindex_table[yylhs as usize] as i32;
        let yydgoto: u16 = yydgoto_table[yylhs as usize] as u16;

        let mut next_state_toks = if yygindex != 0 {
            quote! {
                let next_state: u16 = {
                    let i = #yygindex + self.yystate as i32;
                    if i >= 0 && YYCHECK[i as usize] as u16 == self.yystate {
                        racc_log!("yyreduce: yycheck passes, yytable[{}] = s{}", i, YYTABLE[i as usize] as u16);
                        YYTABLE[i as usize] as u16
                    } else {
                        racc_log!("yyreduce: using default goto {}", #yydgoto);
                        #yydgoto
                    }
                };
            }
        } else {
            // There are no gotos associated with this LHS symbol.
            quote! {
                racc_log!("yyreduce: using default goto {}", #yydgoto);
                let next_state = #yydgoto;
            }
        };

        next_state_toks.extend(quote! {
            self.state_stack.push(self.yystate);
            self.yystate = next_state;
            racc_log!("states: {:?} {}", self.state_stack, self.yystate);
        });

        // If we are reducing a rule for the goal symbol, and yystate is in the initial state,
        // then transition to YYFINAL. Since we are generating code for each rule, we can avoid
        // adding this check for reductions unrelated to the goal symbol.
        if yylhs == 0 {
            next_state_toks = quote! {
                if self.yystate == 0 {
                    racc_log!(
                        "yyreduce: after reduction, shifting to state {} (0/0 case). setting yystate = FINAL.",
                        YYFINAL
                    );
                    self.yystate = YYFINAL;
                } else {
                    #next_state_toks
                }
            };
        }

        extend_stmt_parse_quote_spanned! {
            stmts1,
            rule_span =>
            #next_state_toks
        }

        // We are done generating code for this rule. Add the code to the 'match' that we are
        // building.
        let rule_string = gram.rule_to_str(rule);
        reduction_match.arms.push(parse_quote_spanned! {
            rule_span =>
            #pat_value => {
                let _ = #rule_string;
                #stmts0
                #(#stmts1)*
            }
        });
    }

    // Add the final unreachable!() to the reduction match statement.
    reduction_match.arms.push(parse_quote! {
        _ => unreachable!(),
    });

    errors.with_value(syn::ImplItem::Method(parse_quote! {
        // Performs a reduction.
        #[allow(unused_braces)]
        #[inline(never)]
        fn yyreduce(&mut self, reduction: u16, #context_param)
            -> Result<(), racc_runtime::Error>
        {
            #all_action_funcs

            racc_log!("yyreduce: reducing: {}", YYRULES[reduction as usize]);

            // Invoke the generated "reduce" method.  This method handles popping values from
            // parser.values_stack, and then executing the app-supplied code for this reduction.
            // Because the generated code handles popping items from the stack, it is not
            // necessary for us to consult a 'yylen' table here; that information is implicit.
            // let old_values_len = self.value_stack.len();

            #reduction_match

            Ok(())
        }
    }))
}

fn output_token_to_i16(gram: &Grammar) -> syn::Item {
    let mut arms = TokenStream::new();

    for i in gram.iter_token_syms() {
        let sym_value = gram.value[i.index()];
        let sym_name = &gram.name[i.index()];

        if gram.sym_type[i.index()].is_some() {
            arms.extend(quote! {
                Token::#sym_name(_) => #sym_value,
            });
        } else {
            // No type for this token. This is very common.
            arms.extend(quote! {
                Token::#sym_name => #sym_value,
            });
        }
    }

    parse_quote! {
        fn token_to_i16(t: &Token) -> i16 {
            match t {
                #arms
            }
        }
    }
}

fn output_var_value_enum(gram: &Grammar) -> syn::Item {
    let mut var_variants = TokenStream::new();

    // Do the same for variables.  Variables are handled differently, though.
    for i in gram.iter_var_syms() {
        let sym_name = &gram.name[i.index()];

        if let Some(sym_ty) = &gram.sym_type[i.index()] {
            var_variants.extend(quote! {
                #sym_name(#sym_ty),
            });
        } else {
            // For variables that don't carry a value, we do not generate an enum variant.
            // var_variants.extend(quote! {
            //     #sym_name,
            // });
        }
    }

    parse_quote! {
        #[derive(Debug)]
        enum VarValue {
            #var_variants
        }
    }
}

fn output_token_enum(gram: &Grammar) -> syn::Item {
    let mut token_variants = TokenStream::new();
    for i in gram.iter_token_syms() {
        let sym_name = &gram.name[i.index()];

        if let Some(sym_ty) = &gram.sym_type[i.index()] {
            token_variants.extend(quote! {
                #sym_name(#sym_ty),
            });
        } else {
            // No type for this token. This is very common.
            token_variants.extend(quote! {
                #sym_name,
            });
        }
    }

    parse_quote! {
        #[derive(Debug)]
        pub enum Token {
            #token_variants
        }
    }
}

/// Generates the `token_has_value` function. This function consumes a token, and if it has
/// a value, it pushes it to the token stack.
///
/// This should only be called if the grammar has at least one token that carries a value and at
/// least one token that does not.  Otherwise, the decision is static.
fn output_token_has_value(gram: &Grammar) -> syn::Item {
    let mut pats = TokenStream::new();
    for i in gram.iter_token_syms() {
        let token_name = gram.name(i);
        if gram.sym_type[i.index()].is_some() {
            pats.extend(quote! {
                | Token::#token_name(..)
            });
        }
    }

    parse_quote! {
        fn token_has_value(t: &Token) -> bool {
            match t {
                #pats => true,
                _ => false,
            }
        }
    }
}

/// Generates the `push` method. The `push` function is the main driver for the parser
/// state machine.
fn output_push(
    _gram: &Grammar,
    needs_token_stack: bool,
    any_token_no_value: bool,
    context_param: &TokenStream,
    context_arg: &TokenStream,
) -> syn::ImplItem {
    let shift_token_stmt = if needs_token_stack {
        if any_token_no_value {
            // At least one token does not have a value. This means that we need to insert a
            // dynamic check for whether the token has a value or not.
            quote! {
                if token_has_value(&token) {
                    racc_log!("shifted token: {:?}", token);
                    self.token_stack.push(token);
                } else {
                    racc_log!("shifted token: {:?} (not really -- it has no value)", token);
                }
            }
        } else {
            // All of the tokens carry a value. We do not need a dynamic check, we simply
            // unconditionally insert the token.
            quote! {
                racc_log!("shifted token: {:?}", token);
                self.token_stack.push(token);
            }
        }
    } else {
        quote! {
            // None of the tokens carries a value; we don't have a token stack at all.
            racc_log!("shifted token: {:?} (not really -- it has no value)", token);
        }
    };

    syn::ImplItem::Method(parse_quote! {
        /// Advances the state of the parser by reporting a new token to the parser.
        ///
        /// Calling this method is the equivalent of returning a token (other than `YYEOF`)
        /// from a `yylex()` function in a YACC parser.
        pub fn push(
            &mut self,
            #context_param // no comma
            token: Token,
        ) -> Result<(), racc_runtime::Error> {
            let token_num = token_to_i16(&token);

            racc_log!(
                "------------- push: reading {} ({}) lval {:?} -------------",
                token_num, YYNAME[token_num as usize], token
            );

            racc_log!("states: {:?} {}", self.state_stack, self.yystate);
            racc_log!("values: {:?}", self.value_stack);
            racc_log!("tokens: {:?}", self.token_stack);

            let mut any_reduce = false;

            loop {
                // Check to see if there is a SHIFT action for this (state, token).
                // All of the values in YYSINDEX are either 0 (meaning no shift) or negative.
                // If YYSINDEX[state] is non-zero, then (token + YYSINDEX[state]) gives yyn.

                // Check to see whether we can shift this token. This used to be in a separate
                // function, try_shift. It has been inlined here, so that the borrow checker
                // can verify that we're using Token correctly.

                let shift: i16 = YYSINDEX[self.yystate as usize];
                if shift != 0 {
                    let yyn_i32 = shift as i32 + (token_num as i32);
                    let yyn = yyn_i32 as usize; // intentionally wrapping

                    if let Some(&check_num) = YYCHECK.get(yyn) {
                        if check_num == token_num {
                            let next_state = YYTABLE[yyn] as u16;

                            self.state_stack.push(self.yystate);
                            self.yystate = next_state;
                            racc_log!("states: {:?} {}", self.state_stack, self.yystate);

                            // Token is moved by the statement following this.
                            #shift_token_stmt

                            self.do_default_reductions(#context_arg)?;
                            break;
                        }
                    }
                }

                // We could not shift the token. Check to see whether we can apply any
                // reductions.

                while self.try_reduce(#context_arg token_num)? {
                    any_reduce = true;
                }

                if !any_reduce {
                    // If there is neither a shift nor a reduce action defined for this (state, token),
                    // then we have encountered a syntax error.
                    racc_log!("syntax error!  token is not recognized in this state.");
                    return Err(racc_runtime::Error::SyntaxError);
                }

            }

            racc_log!("states: {:?} {}", self.state_stack, self.yystate);
            racc_log!("values: {:?}", self.value_stack);
            racc_log!("tokens: {:?}", self.token_stack);
            Ok(())
        }
    })
}

fn output_default_reductions_table(default_reductions: &[Rule]) -> syn::Item {
    //  Generate YYDEFRED table.
    let yydefred: Vec<i16> = default_reductions
        .iter()
        .map(|&s| if s != Rule(0) { s.0 - 2 } else { 0 })
        .collect();
    make_table_i16(Ident::new("YYDEFRED", Span::call_site()), &yydefred)
}

fn output_do_default_reductions(
    context_param: &TokenStream,
    context_arg: &TokenStream,
) -> syn::ImplItem {
    parse_quote! {
        // Do default reductions, as long as there are any default reductions.
        // Returns true if we performed at least one default reduction.
        fn do_default_reductions(&mut self, #context_param) -> Result<(), racc_runtime::Error> {
            loop {
                // Keep in mind that the values in YYDEFRED are biased by 2, in order to save
                // space in related tables.
                let defred = YYDEFRED[self.yystate as usize];
                if defred == 0 {
                    return Ok(());
                }
                racc_log!("do_default_reductions: s{} has default reduction r{}", self.yystate, defred + 2);
                self.yyreduce(defred, #context_arg)?;
            }
        }
    }
}

/// Generates the `finish` method. Apps use the `finish` method to indicate that the sequence of
/// input tokens has terminated, and to receive the final output value (if any) from the top-level
/// rule.
fn output_finish(
    gram: &Grammar,
    context_param: &TokenStream,
    context_arg: &TokenStream,
    needs_token_stack: bool,
) -> syn::ImplItem {
    let mut stmts = quote! {
        racc_log!("------------- finish -------------");
        racc_log!("states: {:?} {}", self.state_stack, self.yystate);
        racc_log!("values: {:?}", self.value_stack);
        racc_log!("tokens: {:?}", self.token_stack);

        // Drive reductions using the special 0 token, which is the EOF ($end) token.
        while self.try_reduce(#context_arg 0)? {
            // nothing, just keep going
        }

        racc_log!("values: {:?}", self.value_stack);
        racc_log!("tokens: {:?}", self.token_stack);

        if self.yystate != YYFINAL {
            racc_log!("finish: yystate is not YYFINAL ({}); state is not accepted", YYFINAL);
            return Err(racc_runtime::Error::SyntaxError);
        }
    };

    // All tokens should have been consumed. Verify this now.
    if needs_token_stack {
        stmts.extend(quote! {
            assert!(self.token_stack.is_empty());
        });
    }

    let accept_sym = gram.goal();

    let return_ty: TokenStream;
    if let Some(accept_var_type) = gram.sym_type[accept_sym.index()].as_ref() {
        return_ty = quote!(#accept_var_type);
        let accept_ident = gram.name(accept_sym);
        stmts.extend(quote! {
            // The value stack should contain exactly one value.
            assert_eq!(self.value_stack.len(), 1);
            let accept_value = match self.value_stack.pop().unwrap() {
                VarValue::#accept_ident(v) => v,
                unrecognized => error_invalid_value_in_values_stack(unrecognized),
            };
            racc_log!("accept: {:?}", accept_value);
            return Ok(accept_value);
        });
    } else {
        // The top-level rule does not have a value, so there should be nothing in value_stack.
        return_ty = quote!(());
        stmts.extend(quote! {
            // The value stack should be empty.
            assert!(self.value_stack.is_empty());
            racc_log!("accept:");
            return Ok(());
        });
    }

    syn::ImplItem::Method(parse_quote! {
        /// Pushes the final "end of input" token into the state machine, and checks whether the
        /// grammar has accepted or rejected the sequence of tokens.
        ///
        /// Calling this method is the equivalent of returning `YYEOF` from a `yylex()` function
        /// in a YACC parser.
        pub fn finish(&mut self, #context_param) -> Result<#return_ty, racc_runtime::Error> {
            #stmts
        }
    })
}

fn output_parse(
    context_param: &TokenStream,
    context_arg: &TokenStream,
    return_ty: &TokenStream,
) -> syn::ImplItem {
    syn::ImplItem::Method(parse_quote! {
        /// Parses an input stream of tokens and returns the result value.
        ///
        /// This provides an interface that is similar to the `yyparse()` function generated by
        /// YACC. It handles creating a parser, pushing tokens into it, and getting the final
        /// value that was produced by the parser.
        #[allow(dead_code)]
        pub fn parse<I>(#context_param tokens: I) -> Result<#return_ty, racc_runtime::Error>
        where
            I: IntoIterator<Item = Token>
        {
            let mut parser = Self::default();

            for t in tokens {
                parser.push(#context_arg t)?;
            }

            parser.finish(#context_arg)
        }
    })
}

// Generates the YYLHS table.
fn output_rule_data(gram: &Grammar) -> syn::Item {
    let mut data: Vec<i16> = Vec::new();
    data.push(gram.value[gram.start().index()]);
    for i in 3..gram.nrules {
        data.push(gram.value[gram.rlhs[i].0 as usize]);
    }
    make_table_i16_signed(Ident::new("YYLHS_NOT_USED", Span::call_site()), &data)
}

fn make_symbol_names_table(span: Span, gram: &Grammar) -> syn::Item {
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

fn make_table_string(name: Ident, strings: &[String]) -> syn::Item {
    let strings_len = strings.len();
    let strings: Vec<syn::LitStr> = strings
        .iter()
        .map(|s| syn::LitStr::new(s, name.span()))
        .collect();
    parse_quote! {
        static #name: [&str; #strings_len] = [
            #( #strings ),*
        ];
    }
}

fn make_rule_text_table(span: Span, gram: &Grammar) -> syn::Item {
    let rules: Vec<String> = (2..gram.nrules)
        .map(|rule| gram.rule_to_str(Rule(rule as i16)))
        .collect();
    make_table_string(Ident::new("YYRULES", span), &rules)
}

fn make_states_text_table(span: Span, gram: &Grammar, parser: &YaccParser) -> syn::Item {
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

pub fn make_table_i16(name: Ident, values: &[i16]) -> syn::Item {
    make_table_i16_as_u16(name, values)
}

pub fn make_table_i16_signed(name: Ident, values: &[i16]) -> syn::Item {
    let values_len = values.len();
    parse_quote! {
        static #name: [i16; #values_len] = [
            #(
                #values
            ),*
        ];
    }
}

fn make_table_i16_as_u16(name: Ident, values: &[i16]) -> syn::Item {
    let u_values: Vec<u16> = values.iter().map(|&value| value as u16).collect();
    let values_len = u_values.len();
    parse_quote! {
        static #name: [u16; #values_len] = [
            #(
                #u_values
            ),*
        ];
    }
}
