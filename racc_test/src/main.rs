
//#![feature(plugin, core, std_misc, fixed_size_array, rt)]
#![allow(non_upper_case_globals)]
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(unused_variables)]

//#![plugin(racc)]

extern crate log;
extern crate core;
extern crate racc;

use racc_runtime::{FinishParseResult, ParserState};

struct AppContext {
    x: usize,
}

pub trait GrammarToken {
    fn token_value(&self) -> usize;
}

racc::racc_grammar! {

    // AppContext ctx;
    // Option<i16>;

    PLUS;
    MINUS;
    LPAREN;
    RPAREN;
    NUM;
    IF;
    ELSE;
    COMMA;
    THEN;
    WHILE;
    DO;

    Expr : NUM=x { println!("NUM={:?}", x); x }
        | Expr=arg1 PLUS Expr=arg3 {
            let a = arg1.unwrap();
            let b = arg3.unwrap();
            println!("reduce by addition: {:?} + {:?}", a, b);
            Some(a + b)
        }
        | Expr=arg1 MINUS Expr=arg3 {
            let a = arg1.unwrap();
            let b = arg3.unwrap();
            println!("reduce by sub: {:?} + {:?}", a, b);
            Some(a - b)
        }
        | ParenExpr=a { println!("reduce by parens: {:?}", a); a }
        | IfExpr=a { println!("reduce by if(): {:?}", a); a }
        | WhileExpr=a { println!("reduce by while(): {:?}", a); a }
        ;

    ParenExpr : LPAREN Expr=a RPAREN { println!("grouping, val={:?}", a); a };

    IfExpr : IF ParenExpr=a THEN Expr { None }
        | IF ParenExpr=a THEN Expr ELSE Expr { None };

    WhileExpr : WHILE ParenExpr=a DO Expr { println!("reduce by while: {:?}", a); None };

}

const EOF: u32 = 0;

fn main() {
    let toks = vec![
        (LPAREN, None),
        (NUM, Some(42)),
        (RPAREN, None),
        (PLUS, None),
        (NUM, Some(24)),
    ];

    let mut parser = ParserState::new(get_parser_tables());

    let mut ctx = AppContext { x: 0 };

    for &(tok, lval) in toks.iter() {
        parser.push_token(&mut ctx, tok, lval);
    }

    match parser.finish(&mut ctx) {
        FinishParseResult::Accepted(final_value) => {
            println!("Accepted: {:?}", final_value);
        }
        FinishParseResult::SyntaxError => {
            println!("SyntaxError");
        }
    }
}
