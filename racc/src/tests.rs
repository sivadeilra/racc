use super::*;

#[test]
fn test_foo() {
    use quote::quote;

    env_logger::builder().default_format_timestamp(false).init();

    fn case(description: &str, tokens: proc_macro2::TokenStream) {
        println!("parsing grammar: {} -----", description);
        match syn::parse2::<Grammar>(tokens.clone()) {
            Ok(g) => {
                // println!("replacement: {:#?}", replacement);
                println!("parsed grammar: nrules={}", g.nrules);
            }
            Err(e) => {
                println!("error: {:?}", e);
            }
        }

        let r = crate::grammar2(tokens);
        if let Ok(t) = &r {
            // will it parse?
            println!("will it parse?");
            let tc = t.clone();
            match syn::parse2::<syn::ItemMod>(quote! { mod the_parser { #tc }}) {
                Ok(_parsed_item) => {
                    println!("parsed ok");
                }

                Err(e) => {
                    println!("nope, reparse failed: {:?}", e);
                }
            }
        }
    }

    /*
    case("empty grammar", quote! {});

    case(
        "tokens, but no rules",
        quote! {
            type Context = ();
            type Value = ();

            FOO;
            BAR;
        },
    );
    */

    case(
        "math",
        quote! {
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
                : DefList(defs) {
                    Program { defs }
                }
            ;

            Def -> Def
                : Expr(e) SEMI {
                    Def::Expr(e)
                }
                | FuncDef(f) {
                    Def::Func(f)
                }
            ;

            CommentList
                : // null
                | Comment
                | CommentList Comment
                ;

            DefList -> Vec<Def>
                : DefList(list) Def(item) {
                    list.push(item);
                    list
                }

                | CommentList Def(d) {
                    println!("DefList: from single def");
                    vec![d]
                }

                | {
                    println!("DefList: from empty");
                    Vec::new()
                }
                ;


            Expr -> i32 : NUM(x) {
                println!("NUM={:?}", x);
                x
            }
            | Expr(a) PLUS Expr(b) {
                a + b
            }
            | Expr(a) MINUS Expr(b) {
                a - b
            }
            | Expr(a) DIVIDE Expr(b) {
                println!("{} / {}", a, b);
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
            }
            | Let(e) { e }
            ;

            Let -> i32 : LET IDENT(_id) EQ Expr(e)
            // TODO: this is broken
            /*{
                println!("setting e = {:?}", e);
                e
            }*/
            IN Expr(_f) {
                println!("popping {:?}", e);
                0
            };

            FuncDef -> FuncDef : FN IDENT(name) LPAREN RPAREN LBRACE Expr(body) RBRACE {
                FuncDef {
                    name,
                    body,
                }
            };

            Comment : COMMENT;
        },
    );
}
