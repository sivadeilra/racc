// RACC -- Rust Another Compiler-Compiler
// --------------------------------------
//
// This is a port of Barkeley YACC to Rust.  It runs as a syntax extension, directly in the compiler.
// 
// This port is NOT functional yet.  The front-end (grammar parsing in reader.rs) works, the grammar
// analysis and table-building works, and it is capable of emitting tables into the AST of the program
// being generated.  The last missing piece is the driver code which runs the state machine.  That's
// relatively easy, just haven't finished it yet.

#![crate_type = "dylib"]
#![feature(plugin_registrar)]
#![feature(phase)]
#![feature(quote)]
#![feature(macro_rules)]

#![allow(dead_code)]
#![allow(non_upper_case_globals)]
//#![allow(unused_imports)]

#[phase(plugin, link)]
extern crate log;

extern crate rustc;

// #[phase(plugin, link)]
extern crate syntax;

use syntax::ast;
use syntax::ext::base::{ExtCtxt, MacResult, MacItems};
// use syntax::ext::build::AstBuilder;
use syntax::codemap;
use syntax::parse::token::Token;
use syntax::ptr::P;
use syntax::print::pprust;
use rustc::plugin::Registry;

mod closure;
mod grammar;
mod lalr;
mod lr0;
mod util;
mod warshall;
mod reader;
mod output;
mod mkpar;
pub mod runtime;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    info!("yacc plugin_registrar");
    reg.register_macro("grammar", expand_grammar);
}

fn expand_grammar(cx: &mut ExtCtxt, sp: codemap::Span, tts: &[ast::TokenTree]) -> Box<MacResult+'static> {
    info!("expand_grammar");

    let mut gen_items: Vec<P<ast::Item>> = Vec::new();

    let mut parser = cx.new_parser_from_tts(tts);

    // First, we read a special list of tokens:
    //
    //      <context-type> <context-param> ;
    //     
    let context_type_ident = parser.parse_ty();
    let context_param_ident = parser.parse_ident();
    parser.expect(&Token::Semi);

    // The type of the symbol values (on values.stack)
    let symbol_value_ty = parser.parse_ty();
    parser.expect(&Token::Semi);

    // Read the tokens and rules.

    let (gram, action_blocks, rhs_binding) = reader::read_grammar(sp, &mut parser);

    let lr0 = lr0::compute_lr0(&gram);
    let lalr_out = lalr::run_lalr(&gram, &lr0);
    let yaccparser = mkpar::make_parser(&gram, &lr0, &lalr_out);

    let yacc_items = output::output_parser_to_ast(cx, sp, &gram, &lalr_out.gotos, &yaccparser, action_blocks, rhs_binding, context_type_ident, context_param_ident, symbol_value_ty);
    for it in yacc_items.into_iter() {
        gen_items.push(it);
    }

    debug!("final items:");
    for it in gen_items.iter() {
        debug!("{}", pprust::item_to_string(&**it));
    }

    MacItems::new(gen_items.into_iter())
}
