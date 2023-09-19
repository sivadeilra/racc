# RACC -- Rust Another Compiler-Compiler

This is a port of Barkeley YACC to Rust.  It runs as a procedural macro, and so allows you to
define grammars directly in Rust source code, rather than calling an external tool or writing
a `build.rs` script.

# How to write a grammar

Here is a very brief example of how to use RACC.  This program evaluates a very limited class
of numeric expressions.

In `Cargo.toml:

```toml,ignore
racc = "0.1.0"
```

In your code:

```rust

#[racc::grammar]
mod grammar {
    // This is the list of tokens defined for your grammar. The `Token` type defines the input
    // the generated parser.
    enum Token {
        NUM(i32),
        PLUS,
        MINUS,
        LPAREN,
        RPAREN,
    }

    // Define the rules of your language.  The first rule implicitly defines the goal symbol.
    // Note the presence of '=x' in the rule definitions.  These are name bindings, which RACC
    // uses in order to allow your code blocks (which are in { ... } braces) to access the
    // values for each symbol.  The values come from the value stack in the parser state machine.
    // When you call push_token(), you provide both the token code and the "value" for that token.

    Expr -> i32 : NUM(x) { x };

    Expr : LPAREN Expr(x) RPAREN { x };

    Expr : Expr(left) PLUS Expr(right) {
        // You can put arbitrary code here.
        println!("evaluating: {} + {}", left, right);

        // The value of the action block is used as the
        // value of the rule (reduction).  Note the absence
        // of a semi-colon here.
        left + right
    };

    Expr : Expr(left) MINUS Expr(right) {
        println!("evaluating: {} - {}", left, right);
        left - right
    };
}

use Token::*;

fn main() {
    // The tokens in our input, and their numeric values.
    let tokens = vec![
        LPAREN,
        NUM(50),
        PLUS,
        NUM(25),
        RPAREN,
        MINUS,
        NUM(10),
    ];

    match Parser::parse(tokens.into_iter()) {
        Ok(value) => println!("Accepted: {}", value),
        Err(e) => println!("Syntax error: {:?}", e),
    }
}

```

## Generating a parser

The parser generator (the `racc::grammar!` macro) analyzes your grammar definition and
generates a parser for your grammar. The parser uses lookup tables and generated code. It also
contains the "actions" that you define in your grammar. Actions are code blocks that you provide,
which run when one of the rules defined in your grammar is matched (is "reduced").

## Invoking the parser

You can invoke the parser in two ways: push or pull.

### Pull model

In the pull model, you invoke the `Parser::parse()` function and give it an iterator that
produces tokens. This is the easiest way to invoke the parser; everything happens within the
scope of the `parse()` function call.

```rust,ignore
match Parser::parse(vec![FOO, BAR, /* ... more tokens ... */]) {
    Ok(result) => println!("Parsing produced: {:?}", result),
    Err(e) => println!("Parsing failed: {:?}", e);
}
```

The `parse()` function is generic over its input. It accepts any `Iterator` implementation that
produces the `Token` values defined by your grammar.

### Push model

In the push model, you create an instance of `Parser` and then call `parser.push(..)` to push
tokens into it. Each call to `push()` advances the state of the parser. If the token is not valid
according to the rules defined by your grammar, then `push()` will return an `Err` value; you must
always check the return value of `push()`.

When you are done processing tokens, you can call `parser.finish()` to indicate that there are no
more tokens and to receive the result of parsing.

```rust,ignore
let mut parser = Parser::new();
parser.push(FOO)?;
parser.push(BAR)?;
// ... more tokens ...
match parser.finish() {
    Ok(result) => println!("Parsing produced: {:?}", result),
    Err(e) => println!("Parsing failed: {:?}", e);
}
```

If your token source uses `async`, then you will need to use the push model, since the
`Iterator` trait does not support asynchronous data sources.

## Actions

Most grammars will want to execute an action when certain rules are matched. Actions can be
added at the end of a rule by adding a Rust code block, .e.g `{ ... }`.

The parser generator collects all of the actions and generates a single function which handles
running the correct action when a rule fires.

## Context: Accessing external data during parsing

Many parsers need to access external state. For example, a parser that implements an interpreter
might need to store a table of named variables. RACC supports this by specifying a context type.
For example:

```rust

#[racc::grammar]
mod grammar {
    type Context = MyContext;

    enum Token {
        FOO,
        BAR,
    }

    G : FOO { context.output.push_str("FOO! "); }
      | BAR { context.output.push_str("BAR! "); } ;
}

use Token::*;

#[derive(Default)]
pub struct MyContext {
    output: String,
}

let mut context = MyContext::default();
Parser::parse(&mut context, vec![FOO, FOO, BAR]);
print!("output: {}", context.output);
```


It is often necessary, when imlementing a parser, to access external or "environmental"
state, when executing rule actions.  In C parsers, this is usually done with global
variables.  However, this is not an option in Rust (and would be undesirable, even if
it were an option).

RACC provides a safe means to access such data.  Rules may access an "app context".
When the app calls `push` or `finish`, the app also passes a `&mut` reference
to an "app context" value.  The type of this value can be anything defined by the
application.  (It is necessary to specify the type in the `grammar!` definition.)
Within the scope of the rule action, this value may be accessed by using the identifier
specified in the grammar definition.  In the example above, the identifier is `ctx`,
and the type of the context is `uint`.

## Propagating values through the parsing tree

Rules may optionally produce a value. Rules which consume the output of other rules may use
those values. This allows grammars to propagate data through the parsing tree.

To use this feature, you must specify a type for each (non-terminal) symbol that carries data,
by using `-> <type>` after the left-hand side symbol when defining a rule. A type can only be
specified once per symbol; redundant definitions are not allowed, even if they specify the same
type. Then, to receive values as input for a rule, specify a _binding_ for each symbol on the
right-hand side of a rule, by specifying `<symbol> = <binding>`, where `<symbol>` is a symbol on
the right-hand side of a rule (either a terminal or a non-terminal) and `<binding>` is the name
of the binding for that value.

Tokens may also carry values. For example, an interpreter might define a `LITERAL` token which
contains a literal numeric value.

For example:

```rust
#[racc::grammar]
mod grammar {
    enum Token {
        LITERAL(f64),       // This specifies that LITERAL contains a value.
        PLUS,
        MINUS,
        LPAREN,
        RPAREN,
    }

    // `Expr -> f64` specifies that `Expr` returns `f64`.
    Expr -> f64 : LITERAL(lit) { lit }
         | Expr(a) PLUS Expr(b) { a + b }     // Expr=a and Expr=b specify bindings
         | Expr(a) MINUS Expr(b) { a - b }
         | LPAREN Expr(e) RPAREN { e }
    ;
}

let result: f64 = Parser::parse(
    vec![
        Token::LITERAL(10.0),
        Token::PLUS,
        Token::LITERAL(20.0),
    ]
).unwrap();
assert_eq!(result, 30.0);
```

In this code, `Expr=left` means "match the symbol `Expr` and bind its value to the
name `left` within the scope of the action," and similarly for `Expr=right`.
Instead of using `$$` for setting the value of the rule action, the value of the rule
action is simply the value of the action, when evaluated using the normal rules of Rust.
This is why the action block in the example ends with `left + right` and not `left + right;`.
Ending the action with `;` would mean that the rule evaluates to `()`.

Note that all rules must evaluate to a value, even if that value is `()` or `None`, and
the type of the value must match the type specified in the grammar.  RACC (like Rust) will
not perform any implicit conversions, or insert any implicit `None` values.

If you do not wish to propagate values in this way, you can use a symbol value of `()`.
If you do this, then you may have empty rule actions.

## Finishing parsing

In Berkeley YACC, the lexer indicates the end of an input stream by reporting a `YYEOF`
token.  Because RACC uses a push model rather than a pull model, a RACC-based parser
indicates the end of the input stream by calling the `parser.finish()` method.  The
`finish` method performs any final reductions that are necessary, and then checks whether
the grammar accepts the input.  If the grammar accepts the input, then `finish` will
return `FinishParseResult::Accept(value)`, where `value` is the value of the entire
parse tree.

# License

Berkeley YACC is in the public domain.  From its `README` file:

```text
        Berkeley Yacc is in the public domain.  The data structures and algorithms
    used in Berkeley Yacc are all either taken from documents available to the
    general public or are inventions of the author.  Anyone may freely distribute
    source or binary forms of Berkeley Yacc whether unchanged or modified.
    Distributers may charge whatever fees they can obtain for Berkeley Yacc.
    Programs generated by Berkeley Yacc may be distributed freely.
```

RACC is published under the MIT open-source license, which should be compatible with nearly all
open source needs and should be compatible with the letter and spirit of Berkeley YACC's license.

# Stability

The ideas implemented in YACC are stable and time-tested.  RACC is a port of YACC, and should
be considered unstable.  The implementation may contain porting bugs, where the behavior of
RACC is not faithful to the original YACC.  Rust procedural macros and the ecosystem supporting
them is also still growing and changing.

So if you build anything using RACC, please be aware that both Rust and RACC are still evolving
quickly, and your code may break quickly and without notice.

The original Berkeley YACC contains a strident disclaimer, which is repeated here:

```text
         Berkeley Yacc is distributed with no warranty whatever.  The author
    and any other contributors take no responsibility for the consequences of
    its use.
```

That disclaimer applies to this Rust port, as well.  The author (of the Rust port) makes no
claim of suitability for any purpose, and takes no responsibility for the consequences of its use.

# TODO List

* Allow grammars to specify precedence and associativity.  The underlying code implements
  support for precedence and associativity, exactly as in Berkeley YACC, but this is not
  yet exposed.

* Port a lexical analyzer, too.

# Author

RACC was implemented by Arlie Davis `arlie.davis@gmail.com`.  I did this as an experiment
in porting a well-known (and useful) tool to Rust.  I was also intrigued by Rust's support
for procedural macros, and I wanted to see whether I could implement something interesting
using procedural macros.

# Feedback

Feel free to send me any feedback on RACC to `arlie.davis@gmail.com`.
