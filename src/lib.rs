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
#![allow(unused_imports)]

#[phase(plugin, link)]
extern crate log;

extern crate rustc;

// #[phase(plugin, link)]
extern crate syntax;

use syntax::ast;
use syntax::ext::base::{ExtCtxt, MacResult, MacItems};
use syntax::ext::build::AstBuilder;
use syntax::codemap;
use syntax::ptr::P;
use syntax::print::pprust;
use rustc::plugin::Registry;

use lr0::compute_lr0;
use output::output_parser_to_ast;

mod closure;
mod grammar;
mod lalr;
mod lr0;
mod util;
mod warshall;
mod reader;
mod output;
mod mkpar;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    info!("yacc plugin_registrar");
    reg.register_macro("grammar", expand_grammar);
}


fn expand_grammar(cx: &mut ExtCtxt, sp: codemap::Span, tts: &[ast::TokenTree]) -> Box<MacResult+'static> {
    info!("expand_grammar");

    let mut gen_items: Vec<P<ast::Item>> = Vec::new();

    let (gram, action_blocks, rhs_binding) = reader::read_grammar(cx, sp, tts);
    let lr0 = compute_lr0(&gram);

    debug!("computed LR(0) info");

    let lalr_out = lalr::run_lalr(&gram, &lr0);

    let yaccparser = mkpar::make_parser(&gram, &lr0, &lalr_out);

    // build 'parse' method

    let parse_id = cx.ident_of("parse_grammar");
    let u8_42 = cx.expr_u8(sp, 42u8);
    let parse_body = cx.block_expr(u8_42);

    let ty_u8 = quote_ty!(cx, u8);

    let parse_method = cx.item_fn(sp, parse_id, vec![], ty_u8, parse_body);
    gen_items.push(parse_method);

    let yacc_items = output_parser_to_ast(cx, sp, &gram, &lalr_out.gotos, &yaccparser, action_blocks, rhs_binding);
    for it in yacc_items.into_iter() {
        gen_items.push(it);
    }

    debug!("final items:");
    for it in gen_items.iter() {
        debug!("{}", pprust::item_to_string(&**it));
    }

    MacItems::new(gen_items.into_iter())
}
