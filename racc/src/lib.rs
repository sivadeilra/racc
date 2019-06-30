// RACC -- Rust Another Compiler-Compiler
// --------------------------------------
//
// This is a port of Barkeley YACC to Rust.  It runs as a syntax extension, directly in the compiler.
//
// This port is NOT functional yet.  The front-end (grammar parsing in reader.rs) works, the grammar
// analysis and table-building works, and it is capable of emitting tables into the AST of the program
// being generated.  The last missing piece is the driver code which runs the state machine.  That's
// relatively easy, just haven't finished it yet.

//! RACC is Rust Another Compiler-Compiler.  It is a port of the public domain Berkeley YACC parser
//! generator to Rust.
//!
//! RACC is implemented as a syntax extension.  You write grammar definitions directly in Rust source
//! code.  Then you enable RACC by referencing the `racc` crate and enabling it to function as a plug-in.
//!
//! # How to write a grammar
//!
//! Here is a very brief example of how to use RACC.  This program evaluates a very limited class
//! of numeric expressions.
//!
//! ```rust,ignore
//!
//! #![feature(phase)]
//!
//! #[phase(plugin, link)] extern crate racc;
//!
//! use racc::runtime::{ParserState, ParserTables, FinishParseResult};
//!
//! grammar! {
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
//! RACC is not faithful to the original YACC.  Also, Rust syntax extensions are themselves an
//! experimental feature, and are not slated to be part of the Rust 1.0 language.  (They will still
//! be available in unstable / nightly builds of Rust.)
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
//! * `finish` is probably not strict enough.
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
//! for syntax extensions, and I wanted to see whether I could implement something interesting
//! using syntax extensions.
//!
//! # Feedback
//!
//! Feel free to send me any feedback on RACC to `arlie.davis@gmail.com`.

#![recursion_limit = "256"]
#![warn(rust_2018_idioms)]

mod closure;
mod grammar;
mod lalr;
mod lr0;
mod mkpar;
mod output;
mod ramp_table;
mod reader;
mod util;
mod warshall;

extern crate proc_macro;

use proc_macro2::Span;
use syn::{parse_macro_input, Ident};

// Type aliases
type Symbol = i16;
type Rule = i16;
type State = i16;
type Item = i16;

#[proc_macro]
pub fn racc_grammar(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // println!("hello, world, from racc_grammar");

    let g = parse_macro_input!(tokens as reader::Grammar2);

    /*
    // First, we read a special list of tokens:
    //
    //      <context-type> <context-param> ;
    //
    let context_type_ident = parser.parse_ty();
    let context_param_ident = match parser.parse_ident() {
        Ok(ident) => ident,
        Err(_)    => panic!("Fatal Error at parse_ident")
    };
    parser.expect(&Token::Semi);

    // The type of the symbol values (on values.stack)
    let symbol_value_ty = parser.parse_ty();
    parser.expect(&Token::Semi);
    */

    let context_param_ident = Ident::new("context", Span::call_site());

    // Read the tokens and rules.

    let gram = &g.grammar;

    let lr0 = lr0::compute_lr0(&gram);
    let lalr_out = lalr::run_lalr(&gram, &lr0);
    let yaccparser = mkpar::make_parser(&gram, &lr0, &lalr_out);

    let parser_tokens = output::output_parser_to_ast(
        &gram,
        &lalr_out.gotos,
        &yaccparser,
        &g.rule_blocks,
        &g.rhs_bindings,
        g.app_context_ty,
        context_param_ident,
        g.value_ty,
    );

    // println!("almost done!");
    // println!("{:?}", parser_tokens);
    // return parser_tokens.into();
    return parser_tokens.into();
}
