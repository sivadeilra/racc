#![feature(phase)]
#![allow(non_upper_case_globals)]
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(unused_variables)]

#[phase(plugin, link)]
extern crate log;

#[phase(plugin, link)] extern crate racc;


struct AppContext {
    x: uint
}

pub trait GrammarToken {
    fn token_value(&self) -> uint;
}



grammar! {

    AppContext ctx ;

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

const EOF: u32 = 0;

static NAMES: [&'static str, ..3] = [
	"alpha",
	"beta",
	"gamma"
];

fn main()
{
	println!("test_math_grammar");

	let mut parser: Parser = Parser {
		state_stack: Vec::new(),
		value_stack: Vec::new()
	};

	let toks = vec![
		LPAREN,
		NUM,
		RPAREN,
		PLUS,
		NUM
	];

	for tok in toks.iter() {
		// parse(tok);
		// println!("tok: {}", tok);
	}

    let mut ctx: AppContext = AppContext {
        x: 0
    };

    let mut yystate: uint = 0;
    parser.state_stack.push(yystate as i16); // value on top of stack should always be equal to yystate variable

    let mut tok_iter = toks.into_iter();

    let mut yychar: Option<u32> = None;

    let mut yylval_fake_counter: i16 = 100;

    let mut yylval: i16 = 0;

    loop {
        println!("");
        println!("parser: yystate={}  state_stack = {}, value_stack = {}", yystate, parser.state_stack, parser.value_stack);
        assert!(parser.state_stack.len() > 0);
        assert!(parser.state_stack[parser.state_stack.len() - 1] as uint == yystate);

        // check for default reductions

        let defred = YYDEFRED[yystate];
        if defred != 0 {
            println!("    default reduction: yyn={}", defred);
            yyreduce(&mut parser, defred as uint, &mut ctx, &mut yystate);
            continue;
        }

        // Make sure we have a token.
        let tok: u32 = match yychar {
            Some(t) => t,       // already have a token; yayyy
            None => {
                match tok_iter.next() {
                    None => {
                        println!("    token iterator has reached end");
                        EOF
                    }
                    Some(t) => {
                        println!("    tokenizer: t = {}", SYMBOL_NAMES[t as uint]);
                        yylval = yylval_fake_counter;
                        yylval_fake_counter += 1;
                        t        // got a new token from iterator
                    }
                }
            }
        };

        println!("    current token = {} {}", tok, SYMBOL_NAMES[tok as uint]);

        // Check to see if there is a SHIFT action for this (state, token).
        let shift = YYSINDEX[yystate] as i16;
        if shift != 0 {
            let yyn = shift + (tok as i16);
            if YYCHECK[yyn as uint] as i16 == tok as i16 {
                let next_state = YYTABLE[yyn as uint] as i16;
                println!("    shifting: YYSINDEX[{}] = {}, with bias = {}, next_state = {}", yystate, shift, yyn, next_state);
                assert!(next_state >= 0);
                yystate = next_state as uint;
                parser.state_stack.push(yystate as i16);
                parser.value_stack.push(yylval);
                println!("    value_stack.push(), new len = {}", parser.value_stack.len());
                yychar = None; // "consume" this token, so we get another one on next iter
                continue;
            }
            else {
                println!("    would shift, but CHECK value does not match");
            }
        }

        // Check to see if there is a REDUCE action for this (state, token).
        let red = YYRINDEX[yystate] as i16;
        if red != 0 {
            let yyn = red + (tok as i16);
            println!("    yyn={}", yyn);
            if YYCHECK[yyn as uint] as i16 == tok as i16 {
                println!("    reducing by {}", red);
            }
            else {
                println!("    would shift, but CHECK value does not match");
            }
        }

        // If there is neither a shift nor a reduce action defined for this (state, token),
        // then we have encountered a syntax error.

        println!("syntax error!  token is not recognized in this state.");
        panic!("no shifts, no reductions!!");
    }
}

fn yyreduce(parser: &mut Parser, reduction: uint, ctx: &mut AppContext, yystate: &mut uint) {
    // yylen = reduction

    let len = YYLEN[reduction] as uint;
    let lhs = YYLHS[reduction];

    println!("    reducing by rule {}, len={}, lhs={}", YYRULES[reduction], len, lhs);
    assert!(parser.value_stack.len() >= len);
    assert!(parser.state_stack.len() >= len);

    // Invoke the generated "reduce" method.  This method handles popping values from
    // parser.values_stack, and then executing the app-supplied code for this reduction.
    // Because the generated code handles popping items from the stack, it is not necessary
    // for us to consult a 'yylen' table here; that information is implicit.
    reduce(parser, reduction, ctx);

    let top_state = parser.state_stack[parser.state_stack.len() - 1 - len] as uint;
    // pop state stack
    for _ in range(0, len) {
        parser.state_stack.pop().unwrap();
    }
    let top_state = parser.state_stack[parser.state_stack.len() - 1] as uint;

//    let top_state = parser.state_stack[parser.state_stack.len() - 1] as uint; // peek the top state
    println!("        popped {} states, new top state is {}", len, top_state);
    *yystate = top_state;

    if top_state == 0 && lhs == 0 {
        println!("        after reduction, shifting from state 0 to state {}", YYFINAL);
        *yystate = YYFINAL;
        parser.state_stack.push(YYFINAL as i16);
        parser.value_stack.push(1000); // todo: handle lval

        // todo: port acceptance code
    }
    else {
        let yyn_0 = YYGINDEX[lhs as uint] as i16;
        let yyn_1 = yyn_0 + ((*yystate) as i16);

        println!("        checking gindex, yym={}, yyn_0={}, yyn_1={}, YYCHECK[yyn_1]={}", lhs, yyn_0, yyn_1, YYCHECK[yyn_1 as uint]);
        let next_state: uint = if (YYCHECK[yyn_1 as uint] as uint) == *yystate {
            println!("        yystate = yytable[{}] = {}", yyn_1, YYTABLE[yyn_1 as uint]);
            YYTABLE[yyn_1 as uint] as uint
        }
        else {
            println!("         yystate = yydgoto[{}] = {}", reduction, YYDGOTO[lhs as uint]);
            YYDGOTO[lhs as uint] as uint
        };
        *yystate = next_state;
        parser.state_stack.push(next_state as i16);

        // Push the value that represents the reduction of this rule (the LHS).
        parser.value_stack.push(1000);
    }
}

