#![feature(phase)]
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(unused_variables)]

#[phase(plugin, link)]
extern crate log;

#[phase(plugin, link)] extern crate racc;


grammar! {

	PLUS = '+';
	MINUS = '-';
	LPAREN = '(';
	RPAREN = ')';
	NUM;
	IF;
	ELSE;
	COMMA;
	THEN;
	WHILE;
	DO;

	Expr : NUM
		| Expr=arg1 PLUS Expr=arg3 { println!("reduce by addition: {} + {}", arg1, arg3); }
		| Expr=arg1 MINUS Expr=arg3 { println!("reduce by subtraction: {} - {}", arg1, arg3); }
		| ParenExpr
		| IfExpr
		| WhileExpr;

	ParenExpr : LPAREN Expr RPAREN { println!("grouping"); };

	IfExpr : IF ParenExpr THEN Expr
		| IF ParenExpr THEN Expr ELSE Expr;

	WhileExpr : WHILE ParenExpr DO Expr;

}

static NAMES: [&'static str, ..3] = [
	"alpha",
	"beta",
	"gamma"
];

fn main()
{
	println!("test_math_grammar");

	let n = parse_grammar();
	println!("n = {}", n);

	println!("default_reductions:");
	// println!("{}", yydefred.as_slice());

	let mut p: Parser = Parser {
		state_stack: Vec::new(),
		value_stack: Vec::new()
	};

	p.state_stack.push(0);

//	p.parse()

	let toks = vec![
		Token::LPAREN,
		Token::NUM,
		Token::RPAREN,
		Token::PLUS,
		Token::NUM
	];

	for tok in toks.iter() {
		// parse(tok);
		// println!("tok: {}", tok);
	}

	// parse(Token::End);
	reduce(&mut p, 0);
	reduce(&mut p, 1);
	reduce(&mut p, 2);


}
