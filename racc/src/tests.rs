use super::*;
use quote::quote;

#[static_init::dynamic]
static INIT_LOGGER: () = {
    env_logger::builder().default_format_timestamp(false).init();
};

fn case(description: &str, tokens: proc_macro2::TokenStream) {
    println!("parsing grammar: {} -----", description);

    match Grammar::parse_from_tokens(tokens.clone()) {
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

#[test]
fn test_math() {
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

            rules! {

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
        }
        },
    );
}

#[test]
fn test_css() {
    let input = quote! {

        mod grammar {

        // #[rustfmt::skip]
        // #[allow(non_camel_case_types)]
        // #[derive(Copy, Clone, Eq, PartialEq, Debug)]
        /// foo
        enum Token<'a> {
            IDENT(&'a str),                 // 'foo';
            STRING(&'a str),                // '"foo"';
            NUMBER(&'a str),                // '1.2';
            PERCENTAGE(&'a str),            // '10%';
            DIMENSION((&'a str, &'a str)),    // '1px';
            URI(&'a str),                   // 'url(...)';
            FUNCTION(&'a str),              // 'foo(';
            CDO,                            // '<!--';
            CDC,                            // '-->';
            SEMICOLON,                      // ';';
            IMPORT_SYM,                     // '@import';
            MEDIA_SYM,                      // '@media';
            FONT_FACE_SYM,                  // '@font-face';
            PAGE_SYM,                       // '@page';
            CHARSET_SYM,                    // '@charset';
            IMPORTANT_SYM,
            UNKNOWN_AT_KEYWORD,             // '@foo';
            STAR,                           // '*';
            NAMESPACE(&'a str),             // 'ns|';
            HASH(&'a str),                  // '#foo';
            CLASS(&'a str),                 // '.foo';
            PSEUDO_CLASS(PseudoClass),      // ':xxx';   // :link :visited :active :hover ... :only-of-type :empty [subtype is PseudoClass]
            NTH_FUNCTION,                   // ':nth';   // :nth-child( :nth-last-child( :nth-of-type( :nth-last-of-type( [subtype is PseudoClass]
            LANG_FUNCTION,                  // ':lang(';
            NOT_FUNCTION,                   // ':not(';
            LBRACKET,                       // '[';
            RBRACKET,                       // ']';
            LBRACE,                         // '{';
            RBRACE,                         // '}';
            LPAREN,                         // '(';
            RPAREN,                         // ')';
            DASH,                           // '-';
            PLUS,                           // '+';
            TILDE,                          // '~';
            GREATER,                        // '>';
            COMMA,                          // ',';
            SLASH,                          // '/';
            COLON,                          // ':';
            BANG,                           // '!';
            ATTRIB_OP(AttribOp),            // '=';      // = ~= |= ^= $= *= [subtype is AttribOp]
            EQUAL,                          // '='
            INCLUDES,                       // TODO:
            DASHMATCH,                      // TODO:
            PSEUDO_ELEMENT(PseudoElement),  // '::xx';   // ::before ::after ::first-line ::first-letter [subtype is PseudoElement]
            DELIM,                          // '?';
            INVALID,                        // '"foo';

            EOF,
        }

        rules! {

        // stylesheet
        // : [ CHARSET_SYM STRING ';' ]?
        //   [S|CDO|CDC]* [ import [ CDO S* | CDC S* ]* ]*
        //   [ [ ruleset | media | page ] [ CDO S* | CDC S* ]* ]*
        // ;
        stylesheet : charset_opt import_list ruleset_or_media_or_page_list ;

        charset_opt : CHARSET_SYM STRING SEMICOLON
            | // nothing
            ;

    /*
    import
      : IMPORT_SYM S*
        [STRING|URI] S* media_list? ';' S*
      ;
    */
    import : IMPORT_SYM string_or_uri media_list_opt SEMICOLON;

    import_list : import | import_list import | ;

    string_or_uri : STRING | URI ;

    ruleset_or_media_or_page_list :
        ruleset_or_media_or_page_list ruleset |
        ruleset_or_media_or_page_list media |
        ruleset_or_media_or_page_list page |
        ; // empty



    /*

    media
      : MEDIA_SYM S* media_list '{' S* ruleset* '}' S*
      ;
    */
    media : MEDIA_SYM media_list LBRACE ruleset_list RBRACE ;


    // media_list
    //   : medium [ COMMA S* medium]*
    //   ;
    media_list : medium
        | media_list medium ;

    media_list_opt : media_list | ;

    // medium
    //   : IDENT S*
    //   ;

    medium : IDENT ;

    // page
    //   : PAGE_SYM S* pseudo_page?
    //     '{' S* declaration? [ ';' S* declaration? ]* '}' S*
    //   ;

    page : PAGE_SYM pseudo_page_opt LBRACE declaration_list RBRACE ;

    // pseudo_page
    //   : ':' IDENT S*
    //   ;
    pseudo_page : COLON IDENT SEMICOLON ;
    pseudo_page_opt : pseudo_page | ;

    // operator
    //   : '/' S* | ',' S*
    //   ;
    operator : SLASH | COMMA ;

    // combinator
    //   : '+' S*
    //   | '>' S*
    //   ;
    combinator : PLUS | GREATER ;

    // unary_operator
    //   : '-' | '+'
    //   ;
    unary_operator : DASH | PLUS ;

    unary_operator_opt : unary_operator | ;

    // property
    //   : IDENT S*
    //   ;
    property : IDENT ;

    // ruleset
    //   : selector [ ',' S* selector ]*
    //     '{' S* declaration? [ ';' S* declaration? ]* '}' S*
    //   ;

    ruleset : selector_list LBRACE declaration_list RBRACE ;

    ruleset_list :
        ruleset_list ruleset
        | ruleset
        | ;

    // comma-separated list of selectors
    selector_list : selector_list COMMA selector | selector ;

    // selector
    //   : simple_selector [ combinator selector | S+ [ combinator? selector ]? ]?
    //   ;
    selector : simple_selector ;

    // simple_selector
    //   : element_name [ HASH | class | attrib | pseudo ]*
    //   | [ HASH | class | attrib | pseudo ]+
    //   ;
    simple_selector : element_name ;

    // class
    //   : '.' IDENT
    //   ;

    // element_name
    //   : IDENT | '*'
    //   ;
    element_name : IDENT | STAR ;

    // attrib
    //   : '[' S* IDENT S* [ [ '=' | INCLUDES | DASHMATCH ] S*
    //     [ IDENT | STRING ] S* ]? ']'
    //   ;
    attrib : LBRACKET IDENT attrib_bracket_opt ;
    attrib_bracket_opt : LBRACKET attrib_bracket_first attrib_bracket_2 RBRACKET | ;

    attrib_bracket_first : EQUAL | INCLUDES | DASHMATCH ;
    attrib_bracket_2 : IDENT | STRING ;

    // pseudo
    //   : ':' [ IDENT | FUNCTION S* [IDENT S*]? ')' ]
    //   ;
    pseudo : COLON IDENT
        | COLON FUNCTION pseudo_func_args RPAREN ;
    pseudo_func_args : pseudo_func_args IDENT
        | IDENT
        | ;

    // declaration
    //   : property ':' S* expr prio?
    //   ;
    declaration : property COLON expr prio_opt ;
    declaration_list
        : declaration_list SEMICOLON declaration
        | declaration_list SEMICOLON
        | declaration ;

    // prio
    //   : IMPORTANT_SYM S*
    //   ;
    prio : IMPORTANT_SYM ;
    prio_opt : prio | ;

    // expr
    //   : term [ operator? term ]*
    //   ;
    expr : term
        | expr operator term
        | expr term ;

    // term
    //   : unary_operator?
    //     [ NUMBER S* | PERCENTAGE S* | LENGTH S* | EMS S* | EXS S* | ANGLE S* |
    //       TIME S* | FREQ S* ]
    //   | STRING S* | IDENT S* | URI S* | hexcolor | function
    //   ;

    term : unary_operator_opt term1
        | STRING
        | IDENT
        | URI
        | hexcolor
        | function
        ;

    term1 : NUMBER
        | PERCENTAGE
        | DIMENSION
        // | LENGTH
        // | EMS
        // | EXS
        // | ANGLE
        // | TIME
        // | FREQ
        ;


    // function
    //   : FUNCTION S* expr ')' S*
    //   ;
    function : FUNCTION expr RPAREN ;


    /*
     * There is a constraint on the color that it must
     * have either 3 or 6 hex-digits (i.e., [0-9a-fA-F])
     * after the "#"; e.g., "#000" is OK, but "#abcd" is not.
     */
    // hexcolor
    //   : HASH S*
    //   ;
    hexcolor : HASH ;
        }
    }
        };

    case("css", input);
}
