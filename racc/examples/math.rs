racc::grammar! {
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
        MUL,
        DIV,
        IDENT(String),
        LET,
        EQ,
        IN,
    }

    %left PLUS MINUS;
    %left MUL DIV;

    Expr -> i32 : NUM(x) { x }
    | Expr(a) PLUS Expr(b) { a + b }
    | Expr(a) MINUS Expr(b) { a - b }
    | Expr(a) MUL Expr(b) { a * b }
    | Expr(a) DIV Expr(b) {
        if b == 0 {
            return Err(racc_runtime::Error::AppError);
        }
        a / b
    }
    | LPAREN Expr(inner) RPAREN { inner }
    | IF Expr(predicate) THEN Expr(true_value) {
        if predicate != 0 {
            true_value
        } else {
            0
        }
    }
    | IF Expr(predicate) THEN Expr(true_value) ELSE Expr(false_value) {
        if predicate != 0 {
            true_value
        } else {
            false_value
        }
    };
}

#[test]
fn err_test() {
    let toks = vec![Token::NUM(100), Token::DIV, Token::NUM(0)];
    let result = Parser::parse(toks.into_iter());
    assert_eq!(result, Err(racc_runtime::Error::AppError));
}

#[static_init::dynamic]
static INIT_LOGGER: () = env_logger::builder().default_format_timestamp(false).init();

fn main() {
    println!("This only exists for running tests now.");
}

#[cfg(test)]
mod tests {
    use super::*;

    use Token::*;

    #[cfg(test)]
    fn test_case(expected_result: i32, tokens: Vec<Token>) {
        println!("----- case -----");
        let result: i32 = Parser::parse(tokens).expect("expected parsing to succeed");
        assert_eq!(result, expected_result);
    }

    #[test]
    fn basic_test() {
        test_case(
            33,
            vec![LPAREN, NUM(42), PLUS, NUM(24), RPAREN, DIV, NUM(2)],
        );
    }

    #[test]
    fn prec1() {
        test_case(50, vec![NUM(10), PLUS, NUM(20), MUL, NUM(2)]);
    }

    #[test]
    fn prec2() {
        test_case(17, vec![NUM(3), MUL, NUM(4), PLUS, NUM(5)]);
    }
}
