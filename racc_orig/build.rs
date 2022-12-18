fn main() {
    cc::Build::new()
        .file("btyaccpar.c")
        .file("closure.c")
        .file("error.c")
        .file("graph.c")
        .file("lalr.c")
        .file("lr0.c")
        // .file("main.c")
        .file("mkpar.c")
        .file("mstring.c")
        .file("output.c")
        .file("reader.c")
        .file("symtab.c")
        .file("verbose.c")
        .file("warshall.c")
        .file("yaccpar.c")
        .compile("racc_orig_c");
}
