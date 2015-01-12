// Reads a sequence of Rust tokens, which are provided in the body of a macro invocation,
// and builds a Grammar.

// our grammar for a grammar:
//
// <ident> : <ident> ... | <ident> ... ;    // rule def
// <ident> [ = <literal> ];                 // token def, must precede all rule defs

//
// This code reads a sequence of input tokens, and builds a simple yacc grammar.
// It builds a symbol table (names), which name both tokens and variables of the
// defined grammar.  It also builds the rules of the grammar.  Rules are represented
// as a table of left-hand side symbols (the plhs vector) and a table of right-hand
// side symbols (the ritem vector).  The rhs symbols for all rules are packed into
// a single array, the ritem vector.  Each sequence of rhs symbols (for a single rule)
// are stored sequentially, and each rule is terminated by a NO_ITEM symbol.
//
// As the grammar is parsed, we build a name table.  The name table associates an
// integer with each name, which is an index into the ReaderState.symbols table.
// Other tables, such as plhs and ritem, contain indices into the symbols table.
//
// Because indices are added in the order that they are found in the grammar,
// tokens and variables are mixed together in this table.  After the grammar is
// parsed, it is "packed".  This produces a new table, which lists all tokens,
// then all variables.  The plhs and ritem tables are read, and are used to
// produce several new tables.  

use std::rc::Rc;
use std::collections::HashMap;
use std::iter::repeat;
use std::mem::replace;

use syntax::ast;
use syntax::ast::Block;
use syntax::ptr::P;
use syntax::parse::token::{Token,Ident,BinOp,BinOpToken};
use syntax::parse::parser::Parser;
use syntax::codemap;
use syntax::codemap::Span;

use grammar::{TOKEN, UNDEFINED, PREDEFINED_RULES, PREDEFINED_ITEMS};
use grammar::Grammar;

use std::borrow::BorrowFrom;

const NO_SYMBOL: usize = !0;
const NO_ITEM: usize = !0;

impl BorrowFrom<Rc<String>> for str {
    fn borrow_from(owned: &Rc<String>) -> &str {
        owned.as_slice()
    }
}

// symbol classes
#[derive(Copy,PartialEq,Show)]
enum SymClass {
    Unknown = 0,
    Terminal = 1,
    NonTerminal = 2
}

struct Symbol {
    name: Rc<String>,
    tag: Option<Rc<String>>,
    // value: i16,
    prec: i16,
    class: SymClass,
    assoc: u8,
    span: Span,     // code span which defined this name
}

fn make_symbol(name: &str, span: Span) -> Symbol {
    Symbol {
        name: Rc::new(name.to_string()),
        tag: None,
        // value: UNDEFINED,
        prec: 0,
        class: SymClass::Unknown,
        assoc: TOKEN,
        span: span
    }
}

struct ReaderState {
    /// Contains indices that point into `self.symbols`, or `NO_ITEM`.
    pitem: Vec<usize>,

    /// Contains indices that point into `self.symbols`, or `NO_SYMBOL`.
    plhs: Vec<usize>,

    /// Contains all of the symbols, in the order that they are first encountered.
    symbols: Vec<Symbol>,

    /// A lookup table, which gives you an index into self.symbols
    symbol_table: HashMap<Rc<String>, usize>,

    // used for generating names for anonymous symbols
    gensym: u32,

    last_was_action: bool,

    nitems: usize,
    nrules: usize,
    rprec: Vec<i16>,
    rassoc: Vec<u8>,

    /// The actions (code blocks) provided by the grammar author.
    rule_blocks: Vec<Option<P<Block>>>,

    /// identifier used by grammar for a RHS value, given by =foo
    /// indices are same as rrhs
    rhs_binding: Vec<Option<ast::Ident>>,      
}

impl ReaderState {
    pub fn new() -> ReaderState {
        ReaderState {
            pitem: repeat(NO_ITEM).take(PREDEFINED_ITEMS).collect(),
            plhs: repeat(NO_ITEM).take(PREDEFINED_RULES).collect(),
            rule_blocks: repeat(None).take(PREDEFINED_RULES).collect(),
            rhs_binding: repeat(None).take(PREDEFINED_ITEMS).collect(),
            symbols: Vec::new(),
            symbol_table: HashMap::new(),
            gensym: 1,
            last_was_action: false,
            nitems: PREDEFINED_ITEMS,
            nrules: PREDEFINED_RULES,
            rprec: repeat(0).take(PREDEFINED_RULES).collect(),
            rassoc: repeat(TOKEN).take(PREDEFINED_RULES).collect(),
        }
    }

    // Looks up a symbol in the symbol table, and returns the symbol index
    // (the index within ReaderState.symbols) of that symbol.  If the symbol
    // is not already in the symbol table, then this method adds the symbol.
    pub fn lookup(&mut self, name: &str, span: Span) -> usize {
        if let Some(ii) = self.symbol_table.get(name) {
            // debug!("found {}_{} already in table", name, *ii);
            return *ii;
        }

        let index = self.symbols.len();
        let s = make_symbol(name, span);
        self.symbols.push(s);
        self.symbol_table.insert(Rc::new(name.to_string()), index);
        // debug!("added {}_{} to table", name, index);
        return index;
    }

    pub fn lookup_ref_mut<'a>(&'a mut self, name: &str, span: Span) -> (usize, &'a mut Symbol) {
        let index = self.lookup(name, span);
        (index, &mut self.symbols[index])
    }

    pub fn start_rule(&mut self, lhs: usize, span: Span) {
        assert!(self.symbols[lhs].class == SymClass::NonTerminal);
        assert!(self.plhs.len() == self.nrules);
        assert!(self.rprec.len() == self.nrules);
        assert!(self.rassoc.len() == self.nrules);

        // debug!("  start_rule: r{}: {}_{} -> (at item {}) ...", self.nrules, self.symbols[lhs].name, lhs, self.pitem.len());

        self.plhs.push(lhs);
        self.rprec.push(UNDEFINED);
        self.rassoc.push(TOKEN);

        // nrules is not yet advanced; that happens in end_rule
        drop(span); // will use later
    }
    
    // Terminates the current rule.
    pub fn end_rule(&mut self) {
        let rule = self.nrules;

        assert!(self.plhs.len() == rule + 1);
        assert!(self.rprec.len() == rule + 1);
        assert!(self.rassoc.len() == rule + 1);

        if !self.last_was_action && { if let Some(_) = self.symbols[self.plhs[self.nrules]].tag { true } else { false } } {
            if self.pitem[self.pitem.len() - 1] != NO_ITEM {
                let mut i: usize = self.pitem.len() - 1;
                while (i > 0) && self.pitem[i] != NO_ITEM {
                    i -= 1;
                }
                if self.pitem[i + 1] == NO_ITEM || self.symbols[self.pitem[i + 1]].tag != self.symbols[self.plhs[self.nrules]].tag {
                    warn!("default_action_warning();")
                }
            }
        }

        assert!(self.pitem.len() == self.nitems);
        assert!(self.rule_blocks.len() == self.nrules + (if self.last_was_action { 1 } else { 0 }));

        // Insert a None entry into rule_blocks, if the current rule did not declare an action.
        if !self.last_was_action {
            self.rule_blocks.push(None);
        }
        self.last_was_action = false;

        self.pitem.push(NO_ITEM);
        self.rhs_binding.push(None);

        self.nitems += 1;
        self.nrules += 1;

        assert!(self.rule_blocks.len() == self.nrules);

        // debug!("  end_rule: r{}, lhs={} nitems={}", rule, self.plhs[rule], self.pitem.len());
    }

    /// Adds a new "empty" rule.  A new symbol name is generated, using the pattern $$nn,
    /// where $$ is the literal string "$$" and nn is a number.
    pub fn insert_empty_rule(&mut self, span: Span) {
        self.gensym += 1;
        let symname = format!("$${}", self.gensym);

        debug!("insert_empty_rule: added symbol {}", symname);

        let tag = self.symbols[self.plhs[self.nrules]].tag.clone();
        let sym_index = {
            let (sym_index, sym) = self.lookup_ref_mut(symname.as_slice(), span);
            sym.tag = tag;
            sym.class = SymClass::NonTerminal;
            sym_index
        };

        assert!(self.pitem.len() == self.nitems);
        self.nitems += 2;
        self.pitem.push(NO_ITEM);
        self.pitem.push(sym_index);

        let mut bpp = self.nitems - 2;
        loop {
            let b = self.pitem[bpp - 1];
            self.pitem[bpp] = b;
            if b == NO_ITEM {
                break;
            }
            bpp -= 1;
        }

        // Insert the generated rule right before the current rule, which was
        // written to self.{plhs,rprec,rassoc}[nrules].
        self.plhs.insert(self.nrules, sym_index);        
        self.rprec.insert(self.nrules, 0);        
        self.rassoc.insert(self.nrules, TOKEN);

        self.nrules += 1;
    }

    /// Adds a symbol to the RHS of the current rule being built.
    /// Can only be called between calls to start_rule() and end_rule().
    pub fn add_symbol(&mut self, bp: usize, span: Span, ident: Option<ast::Ident>) {
        assert!(self.pitem.len() == self.nitems);
        assert!(self.rhs_binding.len() == self.nitems);

        if self.last_was_action {
            // If we have encountered a new rhs symbol for the current rule, and immediately
            // prior to this we encountered an action (a code block), then we need to finish
            // this rule, and rewrite the lhs of this rule to produce a new, anonymous lhs
            // non-terminal.  Then we will start a new rule, using the lhs that we were
            // previously using, with one rhs symbol, which is the generated symbol.
            self.insert_empty_rule(span);
            self.last_was_action = false;
        }

        assert!(self.pitem.len() == self.nitems);

        // debug!("    add_symbol: pitem[{}] = {}_{}", self.pitem.len(), self.symbols[bp].name, bp);

        self.nitems += 1;
        self.pitem.push(bp);
        self.rhs_binding.push(ident);
    }

    /// "Packs" the symbol table and the grammar definition.  In the packed form, the
    /// tokens are numbered sequentially, and are followed by the non-terminals.
    pub fn pack_symbols_and_grammar(&mut self, goal_symbol: usize) -> Grammar {
        debug!("");
        debug!("pack_symbols");
        debug!("");

        assert!(goal_symbol < self.symbols.len());
        assert!(self.symbols[goal_symbol].class == SymClass::NonTerminal);

        let nsyms: usize = 2 + self.symbols.len(); // $end and $accept
        let mut ntokens: usize = 1; // $end

        // Count the number of tokens.        
        for sym in self.symbols.iter() {
            if sym.class == SymClass::Terminal {
                ntokens += 1;
            }
        }

        let start_symbol = ntokens;
        let nvars = nsyms - ntokens;

        debug!("ntokens={} nvars={} nsyms={}", ntokens, nvars, nsyms);

        let mut gram_name: Vec<String> = repeat(String::new()).take(nsyms).collect();
        let mut gram_value: Vec<i16> = repeat(0).take(nsyms).collect();
        let mut gram_prec: Vec<i16> = repeat(0).take(nsyms).collect();
        let mut gram_assoc: Vec<u8> = repeat(0).take(nsyms).collect();
        let mut gram_rprec = replace(&mut self.rprec, Vec::new());
        let mut gram_rassoc = replace(&mut self.rassoc, Vec::new());

        // Build the 'v' table, which maps from packed symbols to unpacked symbols.  The size of the
        // v table is the number of packed symbols (nsyms), which is not the same as the number of
        // unpacked symbols.  This is because the $accept and error symbols are not symbols in the
        // unpacked view.  In u = v[p], p is a packed symbol index (a number in the nsyms space),
        // while u is the unpacked symbol.
        let v = {
            let mut v: Vec<usize> = repeat(NO_SYMBOL).take(nsyms).collect(); // symbol indices, which point into reader.symbols[]
            v[0] = NO_SYMBOL; // $end
            v[start_symbol] = NO_SYMBOL; // $accept

            let mut i: usize = 1;                      // packed index for assigning tokens
            let mut j: usize = start_symbol + 1;       // packed index for assigning vars
        
            for s in 0 .. self.symbols.len() {
                match self.symbols[s].class {
                    SymClass::Terminal => { v[i] = s; i += 1; }
                    SymClass::NonTerminal => {v[j] = s; j += 1; }
                    SymClass::Unknown => { panic!("symbol {} has no defined class", self.symbols[s].name); }
                }
            }

            assert!(i == ntokens);
            assert!(j == nsyms);
            for s in 1 .. v.len() {
                assert!(s == start_symbol || v[s] != NO_SYMBOL);
            }
            v
        };

        // Build the remap table.  map_to_packed[old] gives the index of the packed location.
        // This replaces the bucket::index field, from C.  This is the inverse of v.  The "error"
        // symbol is always at packed index 1.
        let mut map_to_packed: Vec<i16> = repeat(-1).take(nsyms).collect();
        map_to_packed[0] = 1; // The 'error' symbol

        for i in (1 .. ntokens) {
            map_to_packed[v[i]] = i as i16;
        }

        map_to_packed[goal_symbol] = (start_symbol + 1) as i16;
        let mut k = start_symbol + 2;
        for i in (ntokens + 1 .. nsyms) {
            if v[i] != goal_symbol {
                map_to_packed[v[i]] = k as i16;
                k += 1;
            }
        }

        // symbols_value replaces the bucket::value field.  that is, for (i, j),
        // self.symbols[i].value = j ==> symbols_value[i] = j
        let mut symbols_value: Vec<i16> = repeat(UNDEFINED).take(self.symbols.len()).collect();

        symbols_value[goal_symbol] = 0;
        let mut k: usize = 1;
        for i in (start_symbol + 1 .. nsyms) {
            if v[i] != goal_symbol {
                symbols_value[v[i]] = k as i16;
                k += 1;
            }
        }

        // Assign token values
        let mut k = 0;
        for i in (1 .. ntokens) {
            let n = symbols_value[v[i]];
            if n > 256 {
                let mut j = k;
                k += 1;
                while j > 0 && gram_value[j - 1] > n {
                    gram_value[j] = gram_value[j - 1];
                    j -= 1;
                }
                gram_value[j] = n as i16;
            }
        }

        if symbols_value[v[1]] == UNDEFINED {
            symbols_value[v[1]] = 256;
        }

        let mut j = 0;
        let mut n = 257;
        for i in (2 .. ntokens) {
            if symbols_value[v[i]] == UNDEFINED {
                while j < k && n == gram_value[j] {
                    while { j += 1; j < k && n == gram_value[j] } {
                        continue;
                    }
                    n += 1;
                }
                symbols_value[v[i]] = n as i16;
                n += 1;
            }
        }

        // Propagate $end token
        gram_name[0] = "$end".to_string();
        gram_value[0] = 0;
        gram_prec[0] = 0;
        gram_assoc[0] = TOKEN;

        // Propagate token symbols
        for i in (1 .. ntokens) {
            let from = &self.symbols[v[i]];
            gram_name[i] = from.name.to_string();
            gram_value[i] = symbols_value[v[i]];
            gram_prec[i] = from.prec;
            gram_assoc[i] = from.assoc;
        }

        // Set up the start (accept) symbol
        assert!(start_symbol == ntokens);
        gram_name[start_symbol] = "$accept".to_string();
        gram_value[start_symbol] = -1;
        gram_prec[start_symbol] = 0;
        gram_assoc[start_symbol] = TOKEN;

        // Propagate non-terminal symbols
        for i in (start_symbol + 1 .. nsyms) {
            let k = map_to_packed[v[i]] as usize;
            assert!(k != NO_SYMBOL);
            let from = &self.symbols[v[i]];
            gram_name[k] = from.name.to_string();
            gram_value[k] = symbols_value[v[i]];
            gram_prec[k] = from.prec;
            gram_assoc[k] = from.assoc;
        }

        debug!("packed symbol table:");
        for i in (0 .. nsyms) {
            debug!("    {:3} {} {:20} value {:3} prec {:2} assoc {:2}", i,
            if i < ntokens { "token" } else { "var  " },
            gram_name[i],
            gram_value[i],
            gram_prec[i],
            gram_assoc[i]);
        }
    
        // Reads the "unpacked" grammar and produces the "packed" grammar.
        //
        // This function implements the second phase of packing.  (The first phase is
        // packing the symbol names).  In this phase, we read self.plhs and self.pitem
        // and create the "packed" ritem, rlhs, rrhs and vectors.  This phase is
        // necessary because plhs contains the "unpacked" symbol indices, and we need
        // the "packed" indices.
        //
        // In the original C code, plhs contained pointers to symbol entries.  However,
        // because we cannot use the same approach with pointers in Rust, plhs contains
        // indices into a separate table (the unpacked symbol table).  It may be possible
        // to simply scan through plhs and remap indices in place, rather than allocating
        // a new array.

        let nitems = self.nitems;
        let nrules = self.nrules;

        // there are three pre-defined rules:
        //      -1 -> (nothing)
        //      -1 -> 
        //      $accept -> start_symbol

        let mut ritem: Vec<i16> = repeat(0).take(nitems).collect();
        ritem[0] = -1;
        ritem[1] = map_to_packed[goal_symbol];
        ritem[2] = 0;
        ritem[3] = -2;

        let mut rlhs: Vec<i16> = repeat(0).take(nrules).collect();
        rlhs[0] = 0;
        rlhs[1] = 0;
        rlhs[2] = start_symbol as i16;

        let mut rrhs: Vec<i16> = repeat(0).take(nrules + 1).collect();
        rrhs[0] = 0;
        rrhs[1] = 0;
        rrhs[2] = 1;

        let plhs = &self.plhs;
        let pitem = &self.pitem;
        let symbols = &self.symbols;

        let mut j = PREDEFINED_ITEMS; // index of next item to process
        for i in (PREDEFINED_RULES .. nrules) {
            rlhs[i] = map_to_packed[plhs[i]] as i16;
            rrhs[i] = j as i16;
            let mut assoc = TOKEN;
            let mut prec2 = 0u8;
            while self.pitem[j] != NO_ITEM {
                ritem[j] = map_to_packed[pitem[j]];
                if symbols[pitem[j]].class == SymClass::Terminal {
                    prec2 = symbols[pitem[j]].prec as u8;
                    assoc = symbols[pitem[j]].assoc;
                }
                j += 1;
            }

            // Terminate the item list with the negative of the rule index.
            // This is important; it is used by the code in lr0::save_reductions()
            // in order to realize when we've reached the end of a rule, and so can
            // emit a reduction in a particular state.
            ritem[j] = -(i as i16);
            j += 1;
            if gram_rprec[i] == UNDEFINED {
                gram_rprec[i] = prec2 as i16;
                gram_rassoc[i] = assoc;
            }
        }

        // Terminate the rrhs list
        rrhs[nrules] = j as i16;

        Grammar {
            nsyms: nsyms,
            ntokens: ntokens,
            nvars: nvars,
            start_symbol: start_symbol,

            name: gram_name,
            pname: Vec::new(),
            value: gram_value,

            prec: gram_prec,
            assoc: gram_assoc,
            
            nitems: nitems,
            nrules: nrules,

            ritem: ritem,
            rlhs: rlhs,
            rrhs: rrhs,    
            rprec: gram_rprec,
            rassoc: gram_rassoc
        }
    }

    pub fn print_grammar(gram: &Grammar) {
        assert!(gram.ritem.len() == gram.nitems);

        debug!("symbols: ntokens={} nvars={} nsyms={}", gram.ntokens, gram.nvars, gram.nsyms);
        for i in 0 .. gram.nsyms {
            if gram.is_var(i) {
                debug!("    {:3}  var    {}", i, gram.name[i]);
            }
            else {
                debug!("    {:3}  token  {}", i, gram.name[i]);
            }
        }
        debug!("");
        debug!("raw items:");

        for i in 0 .. gram.ritem.len() {
            let it = gram.ritem[i];
            if it < 0 {
                debug!("    {:3} --> {:3}", i, it);
            }
            else {
                debug!("    {:3} --> {:3} {}", i, it, gram.name[it as usize]);
            }
        }

        debug!("");
        debug!("rules:");

        let mut k: usize = 1;
        let mut line = String::new();
        for i in 2 .. gram.nrules {
            line.push_str(format!("    [r{:-3} ]   {:-10} : ", i, gram.name[gram.rlhs[i] as usize]).as_slice());
            while gram.ritem[k] >= 0 {
                line.push_str(" ");
                line.push_str(gram.name[gram.ritem[k] as usize].as_slice());
                k += 1;
            }
            k += 1;

            debug!("{}", line);
            line.clear();
        }

        debug!("");
    }
}

// Reads the input of the macro invocation, parses and builds a grammar.
pub fn read_grammar<'a>(grammar_sp: codemap::Span, parser: &mut Parser)
    -> (Grammar, Vec<Option<P<Block>>>, Vec<Option<ast::Ident>>) {

    let mut reader: ReaderState = ReaderState::new();

    // Add the well-known "error" symbol to the table.
    {
        let (_, s) = reader.lookup_ref_mut("error", grammar_sp);
        s.class = SymClass::Terminal;
    }

    // first, parse all tokens.

    let mut goal_symbol: Option<usize> = None;

    // debug!("parsing token definitions");
    loop {
        // debug!("");
        // debug!("token: {}", parser.token);

        match parser.token {
            Token::Eof => {
                debug!("eof");
                break;
            }

            Token::Ident(id, _) => {
                // An identifier can start either a token definition or a rule definition.
                // The next character will tell us whether this is a token definition or a
                // rule definition.
                //      : (begins a rule)
                //      = (defines a token with a specific value)
                //      ; (defines a token with an automatically-assigned value)

                let name_def_str = id.as_str();
                let name_def_span = parser.span;
                let lhs = reader.lookup(name_def_str.as_slice(), name_def_span);

                parser.bump();
            
                match parser.token {
                    Token::Colon => {
                        // debug!("found ':', beginning a rule");
                        parser.bump();
                        match reader.symbols[lhs].class {
                            SymClass::Terminal => {
                                parser.span_err(name_def_span, "name has been defined as a token, and so cannot be on the left-hand side of a rule");
                                parser.span_err(reader.symbols[lhs].span, "see definition of token");
                                // we continue executing, even with a bogus name index.
                            }
                            SymClass::NonTerminal => {
                                // good, this symbol is already known to be a non-terminal
                            }
                            SymClass::Unknown => {
                                // debug!("name '{}' was unknown type, changing to non-terminal (variable)", name_def_str);
                                reader.symbols[lhs].class = SymClass::NonTerminal;
                            }
                        }

                        reader.start_rule(lhs, parser.span);

                        if goal_symbol == None {
                            debug!("using '{}' as start symbol", name_def_str);
                            goal_symbol = Some(lhs);
                        }

                        // In this loop, we process the symbols on the right-hand side of the rule.
                        // If we encounter a symbol (whether token or variable), we add a reference
                        // (a symbol index) to it to prhs.  If we encounter an action definition (code)
                        // then we close the current rule, then peek ahead to see whether we need to
                        // define an unnamed variable for the rule prefix, or whether this is a normal
                        // rule for name_def_str.
                        //
                        // If we encounter a | or ;, then the current rule ends.  If we encounter a |, then
                        // we start a new rule, with the same left-hand symbol.
                        loop {
                            match parser.token {
                                Token::Ident(rhs_ident, _) => {
                                    let rhs_name = rhs_ident.as_str();
                                    // debug!("rule: found token/symbol ref '{}'", rhs_name);                                    
                                    let rhs = reader.lookup(rhs_name.as_slice(), parser.span);
                                    parser.bump();

                                    // see if the symbol is followed by "= binding".
                                    let mut rbind: Option<ast::Ident> = None;
                                    if parser.token == Token::Eq {
                                        parser.bump();
                                        match parser.token {
                                            Token::Ident(rhs_bind_ident, _) => {
                                                // debug!("found rhs binding");
                                                rbind = Some(rhs_bind_ident);
                                                parser.bump();
                                            }
                                            _ => {
                                                parser.unexpected();
                                            }
                                        }
                                    }

                                    reader.add_symbol(rhs, parser.span, rbind);
                                }
                                Token::BinOp(BinOpToken::Or) => {
                                    parser.bump();
                                    reader.end_rule();
                                    reader.start_rule(lhs, name_def_span);
                                }
                                Token::OpenDelim(_) => {
                                    // Parse an action (a code block).  Parsing it is actually very easy, thanks to Rust!
                                    assert!(reader.rule_blocks.len() == reader.nrules);
                                    if reader.last_was_action {
                                        reader.insert_empty_rule(parser.span);
                                    }
                                    let block = parser.parse_block();
                                    reader.rule_blocks.push(Some(block));
                                    reader.last_was_action = true;
                                }
                                Token::Semi => {
                                    parser.bump();
                                    reader.end_rule();
                                    break;
                                }
                                _ => {
                                    parser.unexpected();
                                }
                            }
                        }
                    }
                    Token::Eq | Token::Semi => {
                        // = or ; defines a token
                        let has_value = parser.token == Token::Eq;
                        parser.bump();

                        match reader.symbols[lhs].class {
                            SymClass::Terminal => {
                                // symbol class is already known, but this means user has defined same symbol twice
                                parser.span_err(name_def_span, "token is defined more than once");
                                parser.span_err(reader.symbols[lhs].span, "location of previous definition");
                            }
                            SymClass::NonTerminal => {
                                // this name is defined inconsistently -- as both a variable and a token
                                parser.span_err(name_def_span, "token was previously used as a variable");
                                parser.span_err(reader.symbols[lhs].span, "location of previous definition");
                            }
                            SymClass::Unknown => {
                                // debug!("resolving forward ref of a token '{}'", name_def_str);
                                reader.symbols[lhs].class = SymClass::Terminal;
                            }
                        }

                        // debug!("defining token '{}' at unpacked symbol index {}", name_def_str, lhs);

                        if has_value {
                            match parser.token {
                                Token::Literal(_,_) => {
                                    debug!("token has value: {:?}", parser.token);
                                    parser.bump();
                                    parser.expect(&Token::Semi);
                                }
                                _ => parser.unexpected()
                            }                                                        
                        }
                    }
                    _ => {
                        parser.unexpected();
                    }
                }
            }
            _ => {
                parser.unexpected();
            }
        }
    }

    debug!("");

    // Check that we found a goal state.  This check was in check_symbols().
    // Rebind 'goal_symbol' now that we know it exists.
    let goal_symbol = if let Some(goal) = goal_symbol { goal } else {
        parser.span_err(grammar_sp, "grammar does not define any rules");
        panic!();
    };
    debug!("goal symbol = {}_{}", reader.symbols[goal_symbol].name, goal_symbol);

    // Check for any symbols that were not defined.
    for i in 0 .. reader.symbols.len() {
        let sym = &reader.symbols[i];
        if sym.class == SymClass::Unknown {
            parser.span_err(sym.span, "symbol was used but never defined");
        }
    }
    parser.abort_if_errors();

    let gram = reader.pack_symbols_and_grammar(goal_symbol);
    ReaderState::print_grammar(&gram);

    (gram, reader.rule_blocks, reader.rhs_binding)
}

