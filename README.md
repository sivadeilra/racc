# RACC -- Rust Another Compiler-Compiler

A port of the Berkeley YACC parser-generator to Rust

`racc` is a Rust procedural macro (proc-macro) that allows crates to embed `LALR(1)`
grammars in Rust source code.

## How do I use it?

Look at `racc/examples/math.rs` for a brief example of how to write a grammar.

## What do I do for a lexer?

[nom](https://crates.io/crates/nom) is probably your best bet, for now.

## But, why??

I've always loved `yacc`, and I first ported `yacc` to Rust as a syntax extension, years ago.
This project is mostly an exercise in porting things to Rust, and seeing what the results are.
If it's useful to anyone, then it's useful, and if it's not -- well, it's just anothere
repo, rotting on Github, bothering no one.

Part of the exercise of this port is seeing how C idioms translate into Rust idioms. I find
that porting code to Rust almost invariably clarifies the underlying algorithms, because
concepts like slices and vectors much more clearly express the intent of an algorithm than
C pointers do.

## There are better packages out there, so just give up.

Sure, that's fine. Do whatever you want.

These packages do some or all things better than `racc`:

* https://crates.io/crates/lalrpop - pretty much better in every way
* https://crates.io/crates/nom - good for writing parsers

## Limitations

There are lots of limitations and incomplete aspects of this, unfortunately.
Finding them is left an exercise to the reader.

## Author

RACC was implemented by Arlie Davis `arlie.davis@gmail.com`.  I did this as an experiment
in porting a well-known (and useful) tool to Rust.  I was also intrigued by Rust's support
for procedural macros, and I wanted to see whether I could implement something interesting
using procedural macros.

## Feedback

Feel free to send me any feedback on RACC to `arlie.davis@gmail.com`.
