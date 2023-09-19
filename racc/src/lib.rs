#![doc = include_str!("doc.md")]
#![recursion_limit = "256"]
#![allow(clippy::cognitive_complexity)]
#![allow(clippy::collapsible_else_if)]
#![allow(clippy::needless_lifetimes)]
#![allow(clippy::needless_range_loop)]
#![allow(clippy::too_many_arguments)]
#![allow(unused_imports)]

mod errors;
mod grammar;
mod lalr;
mod lr0;
mod mkpar;
mod output;
mod packing;
mod reader;
mod tvec;
mod util;
mod warshall;

#[cfg(test)]
mod tests;

// use core::fmt::Write;
use core::iter::repeat;
use errors::*;
use grammar::*;
use lalr::GotoMap;
use lalr::LALROutput;
use log::debug;
use lr0::LR0Output;
use mkpar::{ActionCode, YaccParser};
use output::*;
use packing::*;
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::Ident;
use syn::{parse_quote, parse_quote_spanned};
use util::*;

macro_rules! int_alias {
    (type $name:ident = $int:ty;) => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
        struct $name(pub $int);

        impl $name {
            pub fn index(&self) -> usize {
                self.0 as usize
            }
        }

        impl core::ops::Add<$int> for $name {
            type Output = Self;
            fn add(self, rhs: $int) -> $name {
                $name(self.0 + rhs)
            }
        }

        impl core::fmt::Display for $name {
            fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Display::fmt(&self.0, fmt)
            }
        }

        impl core::convert::From<$name> for usize {
            fn from(i: $name) -> usize {
                i.0 as usize
            }
        }

        impl core::convert::From<usize> for $name {
            fn from(i: usize) -> $name {
                $name(i as $int)
            }
        }
    };
}

// Type aliases
int_alias! {type Symbol = i16;}
int_alias! {type Var = i16;}
int_alias! {type Rule = i16;}
int_alias! {type State = i16;}
int_alias! {type Item = i16;}
int_alias! {type Token = i16;}

impl Rule {
    // const RULE_NULL: Rule = Rule(0);
    // const RULE_0: Rule = Rule(0);
    const RULE_1: Rule = Rule(1);
    const RULE_2: Rule = Rule(2);
}

impl Symbol {
    pub const NULL: Symbol = Symbol(0);
    pub const ERROR: Symbol = Token::ERROR.to_symbol();
}

impl Token {
    /// Converts a token to a symbol. This is trivial, since all tokens are symbols
    /// starting at zero.
    pub const fn to_symbol(self) -> Symbol {
        Symbol(self.0)
    }
    pub const ERROR: Token = Token(1);
}

impl Item {
    pub const NULL: Item = Item(0);
}

#[derive(Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
struct SymbolOrRule(i16);

impl SymbolOrRule {
    pub fn rule(rule: Rule) -> SymbolOrRule {
        assert!(rule.0 > 0);
        Self(-rule.0)
    }
    pub fn symbol(symbol: Symbol) -> SymbolOrRule {
        assert!(symbol.0 >= 0);
        Self(symbol.0)
    }
    pub fn is_symbol(self) -> bool {
        self.0 >= 0
    }
    pub fn is_rule(self) -> bool {
        self.0 < 0
    }
    pub fn as_symbol(self) -> Symbol {
        assert!(self.is_symbol());
        Symbol(self.0)
    }
    pub fn as_rule(self) -> Rule {
        assert!(self.is_rule());
        Rule(-self.0)
    }
}

use core::fmt::{Debug, Formatter};
impl Debug for SymbolOrRule {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> core::fmt::Result {
        if self.is_symbol() {
            write!(fmt, "Symbol({})", self.as_symbol().index())
        } else {
            write!(fmt, "Rule({})", self.as_rule().index())
        }
    }
}

type StateOrRule = i16;

#[proc_macro_attribute]
pub fn grammar_mod(
    _attr: proc_macro::TokenStream,
    tokens: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    match syn::parse::<syn::Item>(tokens).unwrap() {
        syn::Item::Mod(input) => {
            let output = do_grammar_mod(input);
            output.into()
        }

        _ => {
            panic!("the #[racc_grammar_mod] attribute can only be applied to mod items");
        }
    }
}

fn do_grammar_mod(mut input: syn::ItemMod) -> TokenStream {
    let mut errors = Errors::default();

    let Some((_brace, content)) = input.content.as_mut() else {
        panic!("{}", "this must be used with a mod definition, i.e. `mod parser { ... }`");
    };

    for item in core::mem::take(content).into_iter() {
        match item {
            syn::Item::Enum(en) if en.ident == "Token" => {
                println!("found enum: {}", en.ident);

                // We process the Token enum, but we also contribute it to the output.
                content.push(syn::Item::Enum(en));
            }

            syn::Item::Macro(m) if m.mac.path.is_ident("rules") => {
                println!("found rules! macro block");
            }

            syn::Item::Type(ty) if ty.ident == "Context" => {
                println!("found Context type alias: {}", ty.ident);
            }

            unknown => {
                errors.push(syn::Error::new(
                    unknown.span(),
                    "unrecognized item. only rule! { ... }, enum Token { ... }, \
                         and type Context = ...; are permitted",
                ));
                content.push(unknown);
            }
        }
    }

    let mut output = input.into_token_stream();
    output.extend(errors.into_token_stream());

    output.extend(quote! {
        pub const FOO: u32 = 42;
    });

    output
}

/// All of the vectors defined in ActionsTable have the same length (nvectors)
/// and the indices are assigned in the same way.
///
/// * S: first region,  length = nstates, contains: shifts
/// * R: second region, length = nstates, contains: reduces
/// * V: third region,  length = nvars,   contains: var stuff
///
/// nvectors = sum of the lengths of these regions = 2 * nstates + gram.nvars
struct ActionsTable {
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

#[cfg(nope)]
#[proc_macro]
pub fn grammar(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let tokens2: proc_macro2::TokenStream = tokens.into();

    match grammar2(tokens2) {
        Ok(result) => result.into(),
        Err(e) => e.into_compile_error().into(),
    }
}

#[proc_macro_attribute]
pub fn grammar(
    _attrs: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    match grammar2(input.into()) {
        Ok(result) => result.into(),
        Err(e) => e.into_compile_error().into(),
    }
}

/// This is the main worker function for the proc macro.
fn grammar2(tokens: proc_macro2::TokenStream) -> syn::Result<proc_macro2::TokenStream> {
    let gram: Grammar = Grammar::parse_from_tokens(tokens)?;

    let lr0 = lr0::compute_lr0(&gram);
    let lalr_out = lalr::run_lalr_phase(&gram, &lr0);
    let parser = mkpar::make_parser(&gram, &lr0, &lalr_out);

    let nstates = parser.nstates();

    let mut act = ActionsTable::new(nstates, gram.nvars);

    let default_reductions = crate::mkpar::default_reductions(&parser.actions);

    token_actions(
        &gram,
        &parser,
        &default_reductions,
        &mut act.froms,
        &mut act.tos,
    );
    let default_goto_table = default_goto_table(nstates, &lalr_out.gotos);
    goto_actions(
        &gram,
        nstates,
        &lalr_out.gotos,
        &default_goto_table,
        &mut act.froms,
        &mut act.tos,
    );
    let order = sort_actions(&act);
    let packed = crate::packing::pack_table(parser.nstates(), &order, &act);

    assert_eq!(gram.rule_blocks.len(), gram.nrules);

    let t = output::output_parser(
        &gram,
        &lr0,
        &lalr_out,
        &default_reductions,
        &default_goto_table,
        &parser,
        &packed,
    );

    Ok(t)
}
