struct AppContext {}

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
    DIVIDE;

    Expr : NUM=x {
        println!("NUM={:?}", x); x
    }
        | Expr=a PLUS Expr=b {
            Some(a.unwrap() + b.unwrap())
        }
        | Expr=a MINUS Expr=b {
            Some(a.unwrap() - b.unwrap())
        }
        | Expr=a DIVIDE Expr=b {
            let a = a.unwrap();
            let b = b.unwrap();
            println!("{} / {}", a, b);
            if b == 0 {
                return Err(racc_runtime::Error::AppError);
            }
            Some(a / b)
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

fn err_test() {
    let toks = vec![(NUM, Some(100)), (DIVIDE, None), (NUM, Some(0))];

    let mut parser = ParserState::new();
    let mut ctx = AppContext {};
    for &(tok, lval) in toks.iter() {
        parser.push_token(&mut ctx, tok, lval).unwrap();
    }
    let result = parser.finish(&mut ctx);
    assert_eq!(result, Err(racc_runtime::Error::AppError));
}

fn main() {
    env_logger::init();

    err_test();
    basic_test();
}

fn basic_test() {
    let toks = vec![
        (LPAREN, None),
        (NUM, Some(42)),
        (RPAREN, None),
        (PLUS, None),
        (NUM, Some(24)),
    ];

    let mut parser = ParserState::new();
    let mut ctx = AppContext {};
    for &(tok, lval) in toks.iter() {
        parser.push_token(&mut ctx, tok, lval).unwrap();
    }
    let result = parser.finish(&mut ctx);
    assert_eq!(result, Ok(Some(66)));
}
