#![allow(non_upper_case_globals)]

extern crate core;
extern crate log;
extern crate racc;

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

    Expr : NUM=x {
        println!("NUM={:?}", x); x
    }
        | Expr=a PLUS Expr=b {
            Some(a.unwrap() + b.unwrap())
        }
        | Expr=a MINUS Expr=b {
            Some(a.unwrap() - b.unwrap())
        }
        | LPAREN Expr=inner RPAREN { inner }
        | IF Expr=predicate THEN Expr=true_value {
            if let Some(p) = predicate {
                if p > 0 {
                    true_value
                } else {
                    None
                }
            } else {
                None
            }
        }
        | IF Expr=predicate THEN Expr=true_value ELSE Expr=false_value {
            if let Some(p) = predicate {
                if p > 0 {
                    true_value
                } else {
                    false_value
                }
            } else {
                false_value
            }
        };

}

fn main() {
    env_logger::init();

    let toks = vec![
        (LPAREN, None),
        (NUM, Some(42)),
        (RPAREN, None),
        (PLUS, None),
        (NUM, Some(24)),
    ];

    let mut parser = new_parser();

    let mut ctx = AppContext { x: 0 };

    for &(tok, lval) in toks.iter() {
        parser.push_token(&mut ctx, tok, lval).unwrap();
    }

    match parser.finish(&mut ctx) {
        Ok(final_value) => {
            println!("Ok: {:?}", final_value);
        }
        Err(e) => {
            println!("Error: {:?}", e);
        }
    }
}
