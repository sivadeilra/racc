#[derive(Debug)]
pub enum Def {
    Expr(i32),
    Func(FuncDef),
}

#[derive(Debug)]
pub struct FuncDef {
    pub name: String,
    pub body: i32,
}

#[derive(Debug)]
pub struct Program {
    pub defs: Vec<Def>,
}

use Token::*;

racc::racc_grammar! {
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
        FN, // the fn keyword
        SEMI, // the semicolon
        LBRACE,
        RBRACE,
        COMMENT,
    }

    Program -> Program
        : DefList=defs {
            Program { defs }
        }
    ;

    Def -> Def
        : Expr=e SEMI {
            Def::Expr(e)
        }
        | FuncDef=f {
            Def::Func(f)
        }
    ;

    CommentList
        : // null
        | Comment
        | CommentList Comment
        ;

    DefList -> Vec<Def>
        : DefList=list Def=item {
            list.push(item);
            list
        }

        | CommentList Def=d {
            println!("DefList: from single def");
            vec![d]
        }

        | {
            println!("DefList: from empty");
            Vec::new()
        }
        ;


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

    Let -> i32 : LET IDENT=_id EQ Expr=e
    // TODO: this is broken
    /*{
        println!("setting e = {:?}", e);
        e
    }*/
     IN Expr=_f {
        println!("popping {:?}", e);
        0
    };

    FuncDef -> FuncDef : FN IDENT=name LPAREN RPAREN LBRACE Expr=body RBRACE {
        FuncDef {
            name,
            body,
        }
    };

    Comment : COMMENT;
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

fn basic_test() {
    let toks = vec![
        LPAREN,
        NUM(42),
        PLUS,
        NUM(24),
        RPAREN,
        DIVIDE,
        NUM(2),
        SEMI,
        // ;
        LPAREN,
        NUM(100),
        MINUS,
        NUM(200),
        RPAREN,
        DIVIDE,
        NUM(2),
        SEMI,
        // ;
        FN,
        IDENT("hello_world".to_string()),
        LPAREN,
        RPAREN,
        LBRACE,
        NUM(1000),
        RBRACE,
    ];

    let program: Program = Parser::parse(toks.into_iter()).expect("parsing should succeed");
    println!("{:#?}", program);

    use core::mem::size_of;
    println!("size_of Token = {}", size_of::<Token>());
    println!("size_of VarValue = {}", size_of::<VarValue>());
}
