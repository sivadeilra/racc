#[racc::grammar]
mod grammar {
    enum Token<'a> {
        // Some of these tokens carry values
        A,
        B(&'a str),
        C((u32, &'a str)),
        D((u32, &'a str)),
    }

    rules! {
        Top : A B C;
    }
}

use Token::*;

#[test]
fn tokens_some_values() {
    let () = Parser::parse(vec![A, B("sparrow"), C((42, "bar"))].into_iter()).unwrap();
}
