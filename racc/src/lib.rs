//! # RACC -- Rust Another Compiler-Compiler
//!
//! This is a port of Barkeley YACC to Rust.  It runs as a procedural macro, and so allows you to
//! define grammars directly in Rust source code, rather than calling an external tool or writing
//! a `build.rs` script.
//!
//! # How to write a grammar
//!
//! Here is a very brief example of how to use RACC.  This program evaluates a very limited class
//! of numeric expressions.
//!
//! In `Cargo.toml:
//!
//! ```toml,ignore
//! racc = "0.1.0"
//! ```
//!
//! In your code:
//!
//! ```rust,ignore
//!
//! racc::grammar! {
//!     uint ctx;    // application context; not used in this example
//!     i32;         // the type of values in the value stack, i.e. %union
//!
//!     // This is the list of tokens defined for your grammar.
//!     // RACC will generate named constants using these names; use those constants
//!     // when calling push_token().
//!     NUM; PLUS; MINUS; LPAREN; RPAREN;
//!
//!     // Define the rules of your language.  The first rule implicitly defines the goal symbol.
//!     // Note the presence of '=x' in the rule definitions.  These are name bindings, which RACC
//!     // uses in order to allow your code blocks (which are in { ... } braces) to access the
//!     // values for each symbol.  The values come from the value stack in the parser state machine.
//!     // When you call push_token(), you provide both the token code and the "value" for that token.
//!
//!     Expr : NUM=x { x };
//!
//!     Expr : LPAREN Expr=x RPAREN { x };
//!
//!     Expr : Expr=left PLUS Expr=right {
//!         // You can put arbitrary code here.
//!         println!("evaluating: {} + {}", left, right);
//!         
//!         // The value of the action block is used as the
//!         // value of the rule (reduction).  Note the absence
//!         // of a semi-colon here.
//!         left + right
//!     };
//!
//!     Expr : Expr=left MINUS Expr=right {
//!         println!("evaluating: {} - {}", left, right);
//!         left - right
//!     };
//! }
//!
//! fn main() {
//!     // The tokens in our input, and their numeric values.
//!     let tokens = vec![
//!         (LPAREN, -1),
//!         (NUM, 50),
//!         (PLUS, -1),
//!         (NUM, 25),
//!         (RPAREN, -1),
//!         (MINUS, -1),
//!         (NUM, 10)
//!     ];
//!
//!     // Create a parser.
//!     let mut parser = new_parser();
//!
//!     let mut ctx: uint = 0; // App context; not used in this example.
//!
//!     for &(token, value) in tokens.iter() {
//!         parser.push_token(&mut ctx, token, value);
//!     }
//!
//!     match parser.finish() {
//!         FinishParseResult::Accept(value) => println!("Accepted: {}", value),
//!         FinishParseResult::SyntaxError => println!("Syntax error")
//!     }
//! }
//! */
//! ```
//!
//! ## Advancing the parser state machine
//!
//! Berkeley YACC generates a `yyparse` function, as the primary entry point to the parser.
//! Your code is integrated into `yyparse` in several ways.  First, `yyparse` will call your
//! `yylex` function in order to read the next token from the input.  Then `yyparse` will
//! advance the state machine, and when rules have been matched ("reduced"), the action code
//! that you provided (in `{ ... }` blocks) will execute.
//!
//! In this model, the `yyparse` method runs until all of the tokens have been processed, or
//! until an action block prematurely exits the parser.  However, this model suffers from
//! several problems.  It puts too much control in the generated code, and requires the
//! parser generator (YACC / RACC) to call into too many "hook" functions, such as `yylex`.
//!
//! Instead, in RACC I have decided to use a different API model.  Instead of generating a
//! `yyparse` function, RACC generates parsing tables and a `reduce` function.  The `reduce`
//! function contains all of the rule action blocks (your code).  RACC also generates a
//! `new_parser` method, which returns a new `ParsingState` struct which contains references
//! to the parsing tables and the generated `reduce` method.  Your app then makes calls
//! to `parser.push_token()` to push tokens into the parser.  This inverts the control-flow
//! model -- your app code is in control, and makes brief calls into the RACC runtime and
//! generated code in order to advance the state of the parser.
//!
//! This is simpler and more flexible, and I hope will be a more natural fit for Rust.
//! This parsing model also works well with Rust's lifetime model.  Each parser object
//! (each instance of `ParsingState`) contains only the state necessary to advance the
//! state machine, and the contents of the "value" stack.
//!
//! ## Accessing external data during parsing
//!
//! It is often necessary, when imlementing a parser, to access external or "environmental"
//! state, when executing rule actions.  In C parsers, this is usually done with global
//! variables.  However, this is not an option in Rust (and would be undesirable, even if
//! it were an option).
//!
//! RACC provides a safe means to access such data.  Rules may access an "app context".
//! When the app calls `push_token` or `finish`, the app also passes a `&mut` reference
//! to an "app context" value.  The type of this value can be anything defined by the
//! application.  (It is necessary to specify the type in the `grammar!` definition.)
//! Within the scope of the rule action, this value may be accessed by using the identifier
//! specified in the grammar definition.  In the example above, the identifier is `ctx`,
//! and the type of the context is `uint`.
//!
//! ## Propagating values through the parsing tree
//!
//! In Berkeley YACC, the tokenizer stage (lexer) may set the `yylval` variable to a value,
//! in order to specify a "value" for the current token.  This value is shifted onto the
//! value stack, and is accessible to rule actions using the `$1` .. `$n` syntax.  Rules
//! specify the result value of the rule by assigning the `$$` value.
//!
//! RACC has a similar facility, but the syntax for using it is different.  The syntax in
//! RACC is a more natural fit for Rust.  Instead of using `$1` bindings, RACC grammars
//! specify name bindings using `= name` after a symbol in a rule definition.  For example:
//!
//! ```rust,ignore
//!     Expr : Expr=left PLUS Expr=right {
//!         println!("evaluating: {} + {}", left, right);
//!         left + right
//!     };
//! ```
//!
//! In this code, `Expr=left` means "match the symbol `Expr` and bind its value to the
//! name `left` within the scope of the action," and similarly for `Expr=right`.
//! Instead of using `$$` for setting the value of the rule action, the value of the rule
//! action is simply the value of the action, when evaluated using the normal rules of Rust.
//! This is why the action block in the example ends with `left + right` and not `left + right;`.
//! Ending the action with `;` would mean that the rule evaluates to `()`.
//!
//! Note that all rules must evaluate to a value, even if that value is `()` or `None`, and
//! the type of the value must match the type specified in the grammar.  RACC (like Rust) will
//! not perform any implicit conversions, or insert any implicit `None` values.
//!
//! If you do not wish to propagate values in this way, you can use a symbol value of `()`.
//! If you do this, then you may have empty rule actions.
//!
//! ## Finishing parsing
//!
//! In Berkeley YACC, the lexer indicates the end of an input stream by reporting a `YYEOF`
//! token.  Because RACC uses a push model rather than a pull model, a RACC-based parser
//! indicates the end of the input stream by calling the `parser.finish()` method.  The
//! `finish` method performs any final reductions that are necessary, and then checks whether
//! the grammar accepts the input.  If the grammar accepts the input, then `finish` will
//! return `FinishParseResult::Accept(value)`, where `value` is the value of the entire
//! parse tree.
//!
//! # License
//!
//! Berkeley YACC is in the public domain.  From its `README` file:
//!
//! ```text
//!         Berkeley Yacc is in the public domain.  The data structures and algorithms
//!     used in Berkeley Yacc are all either taken from documents available to the
//!     general public or are inventions of the author.  Anyone may freely distribute
//!     source or binary forms of Berkeley Yacc whether unchanged or modified.
//!     Distributers may charge whatever fees they can obtain for Berkeley Yacc.
//!     Programs generated by Berkeley Yacc may be distributed freely.
//! ```
//!
//! RACC is published under the MIT open-source license, which should be compatible with nearly all
//! open source needs and should be compatible with the letter and spirit of Berkeley YACC's license.
//!
//! # Stability
//!
//! The ideas implemented in YACC are stable and time-tested.  RACC is a port of YACC, and should
//! be considered unstable.  The implementation may contain porting bugs, where the behavior of
//! RACC is not faithful to the original YACC.  Rust procedural macros and the ecosystem supporting
//! them is also still growing and changing.
//!
//! So if you build anything using RACC, please be aware that both Rust and RACC are still evolving
//! quickly, and your code may break quickly and without notice.
//!
//! The original Berkeley YACC contains a strident disclaimer, which is repeated here:
//!
//! ```text
//!          Berkeley Yacc is distributed with no warranty whatever.  The author
//!     and any other contributors take no responsibility for the consequences of
//!     its use.
//! ```
//!
//! That disclaimer applies to this Rust port, as well.  The author (of the Rust port) makes no
//! claim of suitability for any purpose, and takes no responsibility for the consequences of its use.
//!
//! # TODO List
//!
//! * Allow grammars to specify precedence and associativity.  The underlying code implements
//!   support for precedence and associativity, exactly as in Berkeley YACC, but this is not
//!   yet expose.
//!
//! * Support reading standalone grammars, either using the Rust parser or something else.
//!
//! * Port a lexical analyzer, too.
//!
//! # Author
//!
//! RACC was implemented by Arlie Davis `arlie.davis@gmail.com`.  I did this as an experiment
//! in porting a well-known (and useful) tool to Rust.  I was also intrigued by Rust's support
//! for procedural macros, and I wanted to see whether I could implement something interesting
//! using procedural macros.
//!
//! # Feedback
//!
//! Feel free to send me any feedback on RACC to `arlie.davis@gmail.com`.

#![recursion_limit = "256"]
#![warn(rust_2018_idioms)]
#![allow(clippy::needless_lifetimes)]
#![allow(clippy::cognitive_complexity)]

extern crate proc_macro;

mod grammar;
mod lalr;
mod lr0;
mod mkpar;
mod output;
mod reader;
mod tvec;
mod util;
mod warshall;

use proc_macro2::Span;
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

use reader::GrammarDef;

fn racc_grammar2(tokens: proc_macro2::TokenStream) -> syn::Result<proc_macro2::TokenStream> {
    let grammar_def: GrammarDef = syn::parse2::<GrammarDef>(tokens)?;
    let context_param_ident = Ident::new("context", Span::call_site());
    let gram = &grammar_def.grammar;
    let lr0 = lr0::compute_lr0(&gram);
    let lalr_out = lalr::run_lalr_phase(&gram, &lr0);
    let yaccparser = mkpar::make_parser(&gram, &lr0, &lalr_out);
    Ok(output::output_parser_to_token_stream(
        &gram,
        &lalr_out.gotos,
        &yaccparser,
        &grammar_def.rule_blocks,
        &grammar_def.rhs_bindings,
        grammar_def.context_ty,
        context_param_ident,
        grammar_def.value_ty,
    ))
}

#[proc_macro]
pub fn racc_grammar(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let tokens2: proc_macro2::TokenStream = tokens.into();
    racc_grammar2(tokens2).unwrap().into()
}
