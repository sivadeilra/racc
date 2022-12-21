racc::grammar! {
    enum Token {
        STRING(String),
        INT(i64),
        FLOAT(f64),
        NULL,
        TRUE,
        FALSE,
        LCURLY,
        RCURLY,
        LBRACKET,
        RBRACKET,
        COMMA,
        COLON,
    }

    Value
        : NULL
        | TRUE
        | FALSE
        | FLOAT
        | STRING
        | INT
        | Object
        | Array
    ;

    Object : LCURLY ObjectItemListOrEmpty RCURLY ;

    ObjectItemListOrEmpty
        : ObjectItemList
        |
    ;

    ObjectItemList
        : ObjectItem
        | ObjectItemList COMMA ObjectItem
    ;

    ObjectItem : Value COLON Value ;

    Array : LBRACKET ArrayItemList RBRACKET ;

    ArrayItemList
        : ArrayItemList COMMA Value
        | Value
    ;

    ArrayItemListOrEmpty
        : ArrayItemList
        | // nothing
    ;
}

use Token::*;

fn good_case(tokens: Vec<Token>) {
    println!("---------- case ----------");
    println!("{:?}", tokens);

    let input = format!("{:?}", tokens);

    match Parser::parse(tokens.into_iter()) {
        Ok(()) => {
            println!("successfully parsed.");
        }
        Err(e) => {
            panic!("failed to parse: {:?}\ninput:\n    {}", e, input);
        }
    }
}

macro_rules! case {
    (
        $( $t:tt )*
    ) => {
        {
            let tokens: Vec<Token> = vec![ $( $t )* ];
            good_case(tokens);
        }
    }
}

fn do_err_case(tokens: Vec<Token>) {
    println!("---------- case ----------");
    println!("{:?}", tokens);

    let input = format!("{:?}", tokens);

    match Parser::parse(tokens.into_iter()) {
        Ok(()) => {
            panic!("successfully parsed, which is not what we expected!  input:\n    {}", input);
        }
        Err(e) => {
            println!("as expected, failed to parse: {:?}", e);
        }
    }
}

macro_rules! err_case {
    (
        $( $t:tt )*
    ) => {
        {
            let tokens: Vec<Token> = vec![ $( $t )* ];
            do_err_case(tokens);
        }
    }
}

#[static_init::dynamic]
static INIT_LOGGING_DONE: () = env_logger::builder().default_format_timestamp(false).init();

#[test]
fn test_array() {
    case!(
        LBRACKET,
        TRUE,
        COMMA,
        FALSE,
        COMMA,
        NULL,
        COMMA,
        STRING("Hello!".to_string()),
        RBRACKET,
    );
}

#[test]
fn test_object() {
    case!(
        LCURLY,
        STRING("foo".to_string()),
        COLON,
        STRING("bar".to_string()),
        COMMA,
        INT(42),
        COLON,
        STRING("zap".to_string()),
        RCURLY,
    );
}

#[test]
fn test_bad_object() {
    err_case!(LCURLY);
    err_case!(LCURLY, INT(0), RCURLY);
    err_case!(LCURLY, COMMA, RCURLY);
    err_case!(LCURLY, INT(0), COLON, INT(0), COMMA, RCURLY);
}

