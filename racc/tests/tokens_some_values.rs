racc::racc_grammar! {
    enum Token {
        // Some of these tokens carry any values
        A,
        B(i32),
        C,
    }

    Top : A B C;
}

use Token::*;

#[test]
fn tokens_some_values() {
    let () = Parser::parse(vec![A, B(100), C].into_iter()).unwrap();
}
