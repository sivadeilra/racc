#![doc = include_str!("doc.md")]
#![recursion_limit = "256"]
#![warn(rust_2018_idioms)]
#![allow(clippy::cognitive_complexity)]
#![allow(clippy::collapsible_else_if)]
#![allow(clippy::needless_lifetimes)]
#![allow(clippy::needless_range_loop)]
#![allow(clippy::too_many_arguments)]
#![allow(unused_imports)]

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

// use core::fmt::Write;
use grammar::Grammar;
use log::debug;
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use reader::Errors;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::Ident;

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

fn grammar2(tokens: proc_macro2::TokenStream) -> syn::Result<proc_macro2::TokenStream> {
    let gram: Grammar = syn::parse2::<Grammar>(tokens)?;
    let lr0 = lr0::compute_lr0(&gram);
    let lalr_out = lalr::run_lalr_phase(&gram, &lr0);
    let yaccparser = mkpar::make_parser(&gram, &lr0, &lalr_out);
    Ok(output::output_parser_to_token_stream(
        &gram,
        &lalr_out.gotos,
        &yaccparser,
    ))
}

#[proc_macro]
pub fn grammar(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let tokens2: proc_macro2::TokenStream = tokens.into();

    match grammar2(tokens2) {
        Ok(result) => result.into(),
        Err(e) => e.into_compile_error().into(),
    }
}

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
