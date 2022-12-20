racc::racc_grammar! {
    enum Token {
        // All of these tokens carry any values
        A(i32),
        B(i32),
        C(i32),
    }

    Top : A B C {};
}

use Token::*;

#[test]
fn tokens_all_values() {
    env_logger::builder().default_format_timestamp(false).init();

    let () = Parser::parse(vec![A(1), B(2), C(3)].into_iter()).unwrap();
}
