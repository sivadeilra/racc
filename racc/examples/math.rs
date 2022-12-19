pub trait GrammarToken {
    fn token_value(&self) -> usize;
}

racc::racc_grammar! {
    type Context = ();
    // type Value = Option<i16>;

    enum Token {
        PLUS,
        MINUS,
        LPAREN,
        RPAREN,
        NUM(i32),
        IF,
        ELSE,
        COMMA,
        THEN,
        WHILE,
        DO,
        DIVIDE,
        IDENT(String),
        LET,
        EQ,
        IN,
    }

    Expr -> i32 : NUM=x {
        println!("NUM={:?}", x);
        x
    }
    | Expr=a PLUS Expr=b {
        a + b
    }
    | Expr=a MINUS Expr=b {
        a - b
    }
    | Expr=a DIVIDE Expr=b {
        println!("{} / {}", a, b);
        if b == 0 {
            return Err(racc_runtime::Error::AppError);
        }
        a / b
    }
    | LPAREN Expr=inner RPAREN { inner }
    | IF Expr=predicate THEN Expr=true_value {
        if predicate != 0 {
            true_value
        } else {
            0
        }
    }
    | IF Expr=predicate THEN Expr=true_value ELSE Expr=false_value {
        if predicate != 0 {
            true_value
        } else {
            false_value
        }
    }
    | Let=e { e }
    ;

    Let -> i32 : LET IDENT=id EQ Expr=e {
        println!("setting e = {:?}", e);
        e
    } IN Expr=body {
        println!("popping: id: {:?}, e {:?}, body: {:?}", id, e, body);
        0
    };
}

#[cfg(todo)]
#[racc::racc_grammar_mod]
mod parser {

    enum Token {
        PLUS,
        MINUS,
        LPAREN,
        RPAREN,
        NUM(i32),
        IF,
        ELSE,
        COMMA,
        THEN,
        WHILE,
        DO,
        DIVIDE,
        IDENT(String),
        LET,
        EQ,
        IN,
    }

    fn Expr() -> i32 {
        match .. {
            NUM(value) => value,

            r!(Expr(a) PLUS Expr(b)) => {
                println!("xxx")
            }

            (Expr(a), PLUS, Expr(b)) => {
                println!("{} + {}", a, b);
                a + b
            }
        }
    }

    fn Expr(a: Expr, _: PLUS, b: Expr) -> i32 {
        if a > 10 {
            b
        } else {
            a + 10
        }
    }

    rule!(x, y, {
        if z > 10 {
            z * 10
        } else {
            10
        }
    });

    /*
        Expr -> i32 : NUM=x {
            println!("NUM={:?}", x);
            x
        }
        | Expr=a PLUS Expr=b {
            a + b
        }
        | Expr=a MINUS Expr=b {
            a - b
        }
        | Expr=a DIVIDE Expr=b {
            println!("{} / {}", a, b);
            if b == 0 {
                return Err(racc_runtime::Error::AppError);
            }
            a / b
        }
        | LPAREN Expr=inner RPAREN { inner }
        | IF Expr=predicate THEN Expr=true_value {
            if predicate != 0 {
                true_value
            } else {
                0
            }
        }
        | IF Expr=predicate THEN Expr=true_value ELSE Expr=false_value {
            if predicate != 0 {
                true_value
            } else {
                false_value
            }
        }
        | Let=e { e }
        ;

        Let -> i32 : LET IDENT=id EQ Expr=e {
            println!("setting e = {:?}", e);
            e
        } IN Expr=body {
            println!("popping: id: {:?}, e {:?}, body: {:?}", id, e, body);
            0
        };
    */
}

#[cfg(nope)]
fn err_test() {
    let toks = vec![Token::NUM(100), Token::DIVIDE, Token::NUM(0)];
    let result = Parser::parse(toks.into_iter(), &mut ());
    assert_eq!(result, Err(racc_runtime::Error::AppError));
}

fn main() {
    env_logger::builder().default_format_timestamp(false).init();

    // err_test();
    basic_test();
}

use Token::*;

fn basic_test() {
    let toks = vec![LPAREN, NUM(42), PLUS, NUM(24), RPAREN, DIVIDE, NUM(2)];

    let result = Parser::parse(toks.into_iter(), &mut ()).expect("expected parsing to succeed");
    match result {
        VarValue::Expr(e) => {
            assert_eq!(e, 33);
        }
        unrecognized => {
            panic!("unrecognized output: {:?}", unrecognized);
        }
    }
}
