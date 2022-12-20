racc::racc_grammar! {
    enum Token {
        // None of these tokens carry any values
        A,
        B,
        C,
    }

    Top : A B C;
}

use Token::*;

#[test]
fn tokens_no_values() {
    let () = Parser::parse(vec![A, B, C].into_iter()).unwrap();
}
