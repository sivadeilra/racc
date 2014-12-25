#![feature(phase)]
#![allow(non_upper_case_globals)]
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(unused_variables)]

#[phase(plugin, link)]
extern crate log;

#[phase(plugin, link)] extern crate racc;

use racc::runtime::{ParserState,ParserTables,ParseEndResult};

struct AppContext {
    x: uint
}

pub trait GrammarToken {
    fn token_value(&self) -> uint;
}



grammar! {

    AppContext ctx;
    i16;

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

	Expr : NUM=x { x }
		| Expr=arg1 PLUS Expr=arg3 { 
            let a = arg1;
            let b = arg3;
            println!("reduce by addition: {} + {}", a, b);
            a + b
        }
		| Expr=arg1 MINUS Expr=arg3 {
            let a = arg1;
            let b = arg3;
            println!("reduce by sub: {} + {}", a, b);
            a - b
        }
		| ParenExpr=a { println!("reduce by parens: {}", a); a }
		| IfExpr=a { println!("reduce by if(): {}", a); a }
		| WhileExpr=a { println!("reduce by while(): {}", a); a }
        ;

	ParenExpr : LPAREN Expr=a RPAREN { println!("grouping, val={}", a); a };

	IfExpr : IF ParenExpr=a THEN Expr { a }
		| IF ParenExpr=a THEN Expr ELSE Expr { a };

	WhileExpr : WHILE ParenExpr=a DO Expr { println!("reduce by while: {}", a); -1 };

}

const EOF: u32 = 0;

fn main()
{

	let toks = vec![
		(LPAREN, -1),
		(NUM, 42),
		(RPAREN, -1),
		(PLUS, 24),
		(NUM, -1)
	];

    let mut parser = ParserState::new(ParserTables {
        yyrindex: YYRINDEX.as_slice(),
        yygindex: YYGINDEX.as_slice(),
        yysindex: YYSINDEX.as_slice(),
        yytable: YYTABLE.as_slice(),
        yydefred: YYDEFRED.as_slice(),
        yylen: YYLEN.as_slice(),
        yylhs: YYLHS.as_slice(),
        yycheck: YYCHECK.as_slice(),
        yyfinal: YYFINAL,
        yydgoto: YYDGOTO.as_slice(),
        yyname: YYNAME.as_slice(),

        // debugging
        yyrules: YYRULES.as_slice(),
        reduce: reduce
    });

    let mut ctx = AppContext { x: 0 };

    for &(tok, lval) in toks.iter() {
        let result = parser.push_token(&mut ctx, tok, lval);
        println!("result = {}", result);
    }

    println!("push_end()");
    match parser.push_end(&mut ctx) {
        ParseEndResult::Accepted(final_value) => {
            println!("Accepted: {}", final_value);
        }
        ParseEndResult::SyntaxError => {
            println!("SyntaxError");
        }
    }
}
