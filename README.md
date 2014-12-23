yaccrs
======

A port of the Berkeley YACC parser-generator to Rust

This port is NOT functional yet.  The front-end (grammar parsing in reader.rs) works, the grammar
analysis and table-building works, and it is capable of emitting tables into the AST of the program
being generated.  The last missing piece is the driver code which runs the state machine.  That's
relatively easy, just haven't finished it yet.

