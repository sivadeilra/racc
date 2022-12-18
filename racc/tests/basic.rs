racc::racc_grammar! {

    type Context = ();
    type Value = Option<i16>;

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

// #[test]
fn err_test() {
    let toks = vec![(NUM, Some(100)), (DIVIDE, None), (NUM, Some(0))];

    let mut parser = ParserState::new();
    let mut ctx = ();
    for &(tok, lval) in toks.iter() {
        parser.push_token(&mut ctx, tok, lval).unwrap();
    }
    let result = parser.finish(&mut ctx);
    assert_eq!(result, Err(racc_runtime::Error::AppError));
}

#[test]
fn basic_test() {

    env_logger::builder().default_format_timestamp(false).init();


    let toks = vec![
        (LPAREN, None),
        (NUM, Some(42)),
        (PLUS, None),
        (NUM, Some(24)),
        (RPAREN, None),
        (DIVIDE, None),
        (NUM, Some(2)),
    ];

    let mut parser = ParserState::new();
    let mut ctx = ();
    for &(tok, lval) in toks.iter() {
        parser.push_token(&mut ctx, tok, lval).unwrap();
    }
    let result = parser.finish(&mut ctx);
    assert_eq!(result, Ok(Some(66)));
}
