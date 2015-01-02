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

use syntax::ast;
use syntax::ast::Block;
use syntax::ptr::P;
use syntax::parse::token::{Token,Ident,BinOp,BinOpToken};
use syntax::parse::parser::Parser;
use syntax::codemap;
use syntax::codemap::Span;


use grammar::{TOKEN,UNDEFINED};
use grammar::Grammar;

const NO_SYMBOL: uint = !0u;
const NO_ITEM: uint = !0u;

// symbol classes
#[deriving(Copy,PartialEq,Show)]
enum SymClass {
    Unknown = 0,
    Terminal = 1,
    NonTerminal = 2
}

struct Bucket
{
    name: String,
    tag: Option<Rc<String>>,
    value: i16,
    prec: i16,
    class: SymClass,
    assoc: u8,
    span: Span,     // code span which defined this name
}

fn make_bucket(name: &str, span: Span) -> Bucket
{
    Bucket {
        name: name.to_string(),
        tag: None,
        value: UNDEFINED,
        prec: 0,
        class: SymClass::Unknown,
        assoc: TOKEN,
        span: span
    }
}

struct ReaderState
{
    pitem: Vec<uint>,       // contains indices that point into symbols
    plhs: Vec<uint>,        // contains indices that point into symbols

    // All of the symbols, in the order that they are first encountered.
    symbols: Vec<Bucket>,

    // a lookup table, which gives you an index into self.symbols
    symbol_table: HashMap<String, uint>,

    gensym: uint,          // used for generating names for anonymous symbols

    last_was_action: bool,

    gram: Grammar,         // the grammar we are building

    // The actions (code blocks) provided by the grammar author.
    rule_blocks: Vec<Option<P<Block>>>,

    // identifier used by grammar for a RHS value, given by =foo
    // indices are same as rrhs
    rhs_binding: Vec<Option<ast::Ident>>,      
}

impl ReaderState
{
    pub fn new() -> ReaderState {
        let gram = Grammar::new();
        ReaderState {
            pitem: repeat(NO_ITEM).take(gram.nitems).collect(),
            plhs: repeat(NO_ITEM).take(gram.nrules).collect(),
            rule_blocks: repeat(None).take(gram.nrules).collect(),
            rhs_binding: repeat(None).take(gram.nitems).collect(),
            symbols: Vec::new(),
            symbol_table: HashMap::new(),
            gensym: 1,
            last_was_action: false,
            gram: gram,
        }
    }

    // Looks up a symbol in the symbol table, and returns the symbol index
    // (the index within ReaderState.symbols) of that symbol.  If the symbol
    // is not already in the symbol table, then this method adds the symbol.
    pub fn lookup(&mut self, name: &str, span: Span) -> uint
    {
        if let Some(ii) = self.symbol_table.get(name) {
            // debug!("found {}_{} already in table", name, *ii);
            return *ii;
        }

        let index = self.symbols.len();
        let bp = make_bucket(name, span);
        self.symbols.push(bp);
        self.symbol_table.insert(name.to_string(), index);
        // debug!("added {}_{} to table", name, index);
        return index;
    }

    pub fn lookup_ref_mut<'a>(&'a mut self, name: &str, span: Span) -> (uint, &'a mut Bucket)
    {
        let index = self.lookup(name, span);
        (index, &mut self.symbols[index])
    }

    pub fn start_rule(&mut self, lhs: uint, span: Span)
    {
        assert!(self.symbols[lhs].class == SymClass::NonTerminal);
        assert!(self.plhs.len() == self.gram.nrules);
        assert!(self.gram.rprec.len() == self.gram.nrules);
        assert!(self.gram.rassoc.len() == self.gram.nrules);

        // debug!("  start_rule: r{}: {}_{} -> (at item {}) ...", self.gram.nrules, self.symbols[lhs].name, lhs, self.pitem.len());

        self.plhs.push(lhs);
        self.gram.rprec.push(UNDEFINED);
        self.gram.rassoc.push(TOKEN);

        // nrules is not yet advanced; that happens in end_rule
        drop(span); // will use later
    }
    
    pub fn end_rule(&mut self)
    {
        let rule = self.gram.nrules;

        assert!(self.plhs.len() == rule + 1);
        assert!(self.gram.rprec.len() == rule + 1);
        assert!(self.gram.rassoc.len() == rule + 1);

        if !self.last_was_action && { if let Some(_) = self.symbols[self.plhs[self.gram.nrules]].tag { true } else { false } } {
            if self.pitem[self.pitem.len() - 1] != NO_ITEM {
                let mut i: uint = self.pitem.len() - 1;
                while (i > 0) && self.pitem[i] != NO_ITEM {
                    i -= 1;
                }
                if self.pitem[i + 1] == NO_ITEM || self.symbols[self.pitem[i + 1]].tag != self.symbols[self.plhs[self.gram.nrules]].tag {
                    warn!("default_action_warning();")
                    // default_action_warning();
                }
            }
        }

        assert!(self.pitem.len() == self.gram.nitems);
        assert!(self.rule_blocks.len() == self.gram.nrules + (if self.last_was_action { 1 } else { 0 }));

        // Insert a None entry into rule_blocks, if the current rule did not declare an action.
        if !self.last_was_action {
            self.rule_blocks.push(None);
        }
        self.last_was_action = false;

        self.pitem.push(NO_ITEM);
        self.rhs_binding.push(None);

        self.gram.nitems += 1;
        self.gram.nrules += 1;

        assert!(self.rule_blocks.len() == self.gram.nrules);

        // debug!("  end_rule: r{}, lhs={} nitems={}", rule, self.plhs[rule], self.pitem.len());
    }

    pub fn insert_empty_rule(&mut self, span: Span)
    {
        let nrules = self.gram.nrules;

        self.gensym += 1;
        let symname = format!("$${}", self.gensym);

        debug!("insert_empty_rule: added symbol {}", symname);

        let tag = self.symbols[self.plhs[nrules]].tag.clone();
        let bp = {
            let (bp_index, sym) = self.lookup_ref_mut(symname.as_slice(), span);
            sym.tag = tag;
            sym.class = SymClass::NonTerminal;
            bp_index
        };

        assert!(self.pitem.len() == self.gram.nitems);
        self.gram.nitems += 2;
        self.pitem.push(NO_ITEM);
        self.pitem.push(NO_ITEM);

        let mut bpp = self.gram.nitems - 1;
        self.pitem[bpp] = bp;
        bpp -= 1;
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
        self.plhs.insert(nrules, bp);        
        self.gram.rprec.insert(nrules, 0);        
        self.gram.rassoc.insert(nrules, TOKEN);

        self.gram.nrules += 1;
    }

    pub fn add_symbol(&mut self, bp: uint, span: Span, ident: Option<ast::Ident>)
    {
        assert!(self.pitem.len() == self.gram.nitems);
        assert!(self.rhs_binding.len() == self.gram.nitems);

        if self.last_was_action {
            // If we have encountered a new rhs symbol for the current rule, and immediately
            // prior to this we encountered an action (a code block), then we need to finish
            // this rule, and rewrite the lhs of this rule to produce a new, anonymous lhs
            // non-terminal.  Then we will start a new rule, using the lhs that we were
            // previously using, with one rhs symbol, which is the generated symbol.
            self.insert_empty_rule(span);
            self.last_was_action = false;
        }

        assert!(self.pitem.len() == self.gram.nitems);

        // debug!("    add_symbol: pitem[{}] = {}_{}", self.pitem.len(), self.symbols[bp].name, bp);

        self.gram.nitems += 1;
        self.pitem.push(bp);
        self.rhs_binding.push(ident);
    }

    // TODO: Modify this so that it takes &self, and produces a new set of tables
    // which contain the packed symbols.  This should produce 
    // struct SymbolTable {
    //      names: Vec<String>,
    //      values: Vec<i16>,
    //      prec: Vec<u8>,
    //      assoc: Vec<u8>,
    //      start: uint,
    // }
    //
    // As well as a vector, which allows mapping from old indices to new indices.
    //
    // Returns a vector which maps from old (unpacked) symbol indices to packed
    // symbol indices.  This replaces the bucket.index field.
    pub fn pack_symbols(&mut self, goal_symbol: uint) -> Vec<i16>
    {
        debug!("");
        debug!("pack_symbols");
        debug!("");

        // output/mutated: m_goal

        assert!(self.gram.name.len() == 0);
        assert!(self.gram.value.len() == 0);
        assert!(self.gram.pname.len() == 0);
        assert!(self.gram.prec.len() == 0);
        assert!(self.gram.assoc.len() == 0);        

        assert!(goal_symbol < self.symbols.len());
        assert!(self.symbols[goal_symbol].class == SymClass::NonTerminal);

        for i in range(0, self.symbols.len()) {
            debug!("    [{}] = {} value {}", i, self.symbols[i].name, self.symbols[i].value);
        }

        let nsyms: uint = 2 + self.symbols.len(); // $end and $accept
        let mut ntokens: uint = 1; // $end

        // Count the number of tokens.        
        for sym in self.symbols.iter() {
            if sym.class == SymClass::Terminal {
                ntokens += 1;
            }
        }

        let start_symbol = ntokens;
        let nvars = nsyms - ntokens;

        debug!("ntokens={} nvars={} nsyms={}", ntokens, nvars, nsyms);

        self.gram.name.extend(repeat(String::new()).take(nsyms));
        self.gram.value.extend(repeat(0).take(nsyms));
        self.gram.prec.extend(repeat(0).take(nsyms));
        self.gram.assoc.extend(repeat(0).take(nsyms));

        // debug!("building v table");

        // Build the 'v' table, which maps from packed symbols to packed symbols.  The size of the
        // v table is the number of packed symbols (nsyms), which is not the same as the number of
        // unpacked symbols.  This is because the $accept and error symbols are not symbols in the
        // unpacked view.  In u = v[p], p is a packed symbol index (a number in the nsyms space),
        // while u is the unpacked symbol.
        let v = {
            let mut v: Vec<uint> = repeat(NO_SYMBOL).take(nsyms).collect(); // symbol indices, which point into reader.symbols[]
            v[0] = NO_SYMBOL; // $end
            v[start_symbol] = NO_SYMBOL; // $accept

            let mut i: uint = 1;                      // packed index for assigning tokens
            let mut j: uint = start_symbol + 1;       // packed index for assigning vars
        
            for s in range(0, self.symbols.len()) {
                match self.symbols[s].class {
                    SymClass::Terminal => { v[i] = s; i += 1; }
                    SymClass::NonTerminal => {v[j] = s; j += 1; }
                    SymClass::Unknown => { panic!("symbol {} has no defined class", self.symbols[s].name); }
                }
            }

            assert!(i == ntokens);
            assert!(j == nsyms);
            for s in range(1, v.len()) {
                assert!(s == start_symbol || v[s] != NO_SYMBOL);
            }
            v
        };

        /*
        debug!("v table (maps packed to unpacked):");
        for i in range(0, v.len()) { 
            if v[i] == NO_SYMBOL {
                debug!("    packed {:3} --> NO_SYMBOL", i);
            }
            else {
                debug!("    packed {:3} --> {}_{}", i, self.symbols[v[i]].name, v[i]);
            }
        }*/

        // Build the remap table.  map_to_packed[old] gives the index of the packed location.
        // This replaces the bucket::index field, from C.  This is the inverse of v.  The "error"
        // symbol is always at packed index 1.
        let mut map_to_packed: Vec<i16> = repeat(-1).take(nsyms).collect();
        map_to_packed[0] = 1; // The 'error' symbol

        for i in range(1, ntokens) {
            map_to_packed[v[i]] = i as i16;
        }

        map_to_packed[goal_symbol] = (start_symbol + 1) as i16;
        let mut k = start_symbol + 2;
        for i in range(ntokens + 1, nsyms) {
            if v[i] != goal_symbol {
                map_to_packed[v[i]] = k as i16;
                k += 1;
            }
        }

        self.symbols[goal_symbol].value = 0;
        let mut k: uint = 1;
        for i in range(start_symbol + 1, nsyms) {
            if v[i] != goal_symbol {
                self.symbols[v[i]].value = k as i16;
                k += 1;
            }
        }

        // Assign token values
        let mut k = 0;
        for i in range(1, ntokens) {
            let n = self.symbols[v[i]].value;
            if n > 256 {
                let mut j = k;
                k += 1;
                while j > 0 && self.gram.value[j - 1] > n {
                    self.gram.value[j] = self.gram.value[j - 1];
                    j -= 1;
                }
                self.gram.value[j] = n as i16;
            }
        }

        if self.symbols[v[1]].value == UNDEFINED {
            self.symbols[v[1]].value = 256;
        }

        let mut j = 0;
        let mut n = 257;
        for i in range(2, ntokens) {
            if self.symbols[v[i]].value == UNDEFINED {
                while j < k && n == self.gram.value[j] {
                    while { j += 1; j < k && n == self.gram.value[j] } {
                        continue;
                    }
                    n += 1;
                }
                self.symbols[v[i]].value = n as i16;
                n += 1;
            }
        }

        // Propagate $end token
        self.gram.name[0] = "$end".to_string();
        self.gram.value[0] = 0;
        self.gram.prec[0] = 0;
        self.gram.assoc[0] = TOKEN;

        // Propagate token symbols
        for i in range(1, ntokens) {
            let from = &self.symbols[v[i]];
            self.gram.name[i] = from.name.to_string();
            self.gram.value[i] = from.value;
            self.gram.prec[i] = from.prec;
            self.gram.assoc[i] = from.assoc;
        }

        // Set up the start (accept) symbol
        assert!(start_symbol == ntokens);
        self.gram.name[start_symbol] = "$accept".to_string();
        self.gram.value[start_symbol] = -1;
        self.gram.prec[start_symbol] = 0;
        self.gram.assoc[start_symbol] = TOKEN;

        // Propagate non-terminal symbols
        for i in range(start_symbol + 1, nsyms) {
            let k = map_to_packed[v[i]] as uint;
            assert!(k != NO_SYMBOL);
            let from = &self.symbols[v[i]];
            self.gram.name[k] = from.name.to_string();
            self.gram.value[k] = from.value;
            self.gram.prec[k] = from.prec;
            self.gram.assoc[k] = from.assoc;
        }

/* todo
        let symbol_pname: Vec<String> = Vec::new();
        if gflag {
            for i in range(0, nsyms) {
                let pname = protect_string(reader.gram.name[i]);
                symbol_pname.push(pname);
            }
        }
*/

        self.gram.nsyms = nsyms;
        self.gram.ntokens = ntokens;
        self.gram.nvars = nvars;
        self.gram.start_symbol = start_symbol;

        debug!("packed symbol table:");
        for i in range(0, nsyms) {
            debug!("    {:3} {} {:20} value {:3} prec {:2} assoc {:2}", i,
            if i < ntokens { "token" } else { "var  " },
            self.gram.name[i],
            self.gram.value[i],
            self.gram.prec[i],
            self.gram.assoc[i]);
        }
    
        map_to_packed
    }

    pub fn pack_grammar(&mut self, map_to_packed: &[i16], goal_var: uint)
    {
        let nitems = self.gram.nitems;
        let nrules = self.gram.nrules;

        // there are three pre-defined rules:
        //      -1 -> (nothing)
        //      -1 -> 
        //      $accept -> start_symbol

        let mut ritem: Vec<i16> = repeat(0).take(nitems).collect();
        ritem[0] = -1;
        ritem[1] = map_to_packed[goal_var];
        ritem[2] = 0;
        ritem[3] = -2;

        let mut rlhs: Vec<i16> = repeat(0).take(nrules).collect();
        rlhs[0] = 0;
        rlhs[1] = 0;
        rlhs[2] = self.gram.start_symbol as i16;

        let mut rrhs: Vec<i16> = repeat(0).take(nrules + 1).collect();
        rrhs[0] = 0;
        rrhs[1] = 0;
        rrhs[2] = 1;

        let plhs = &self.plhs;
        let pitem = &self.pitem;
        let symbols = &self.symbols;

        let gram = &mut self.gram;

        let mut j = 4; // index of next item to process
        for i in range(3, nrules) {
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
            if gram.rprec[i] == UNDEFINED {
                gram.rprec[i] = prec2 as i16;
                gram.rassoc[i] = assoc;
            }
        }

        // Terminate the rrhs list
        rrhs[nrules] = j as i16;

        // Store results
        gram.rlhs = rlhs;
        gram.rrhs = rrhs;    
        gram.ritem = ritem;
    }

    pub fn print_grammar(gram: &Grammar)
    {
        assert!(gram.ritem.len() == gram.nitems);

        let mut k: uint = 1;

        debug!("symbols: ntokens={} nvars={} nsyms={}", gram.ntokens, gram.nvars, gram.nsyms);
        for i in range(0, gram.nsyms) {
            if gram.is_var(i) {
                debug!("    {:3}  var    {}", i, gram.name[i]);
            }
            else {
                debug!("    {:3}  token  {}", i, gram.name[i]);
            }
        }
        debug!("");
        debug!("raw items:");

        for i in range(0, gram.ritem.len()) {
            let it = gram.ritem[i];
            if it < 0 {
                debug!("    {:3} --> {:3}", i, it);
            }
            else {
                debug!("    {:3} --> {:3} {}", i, it, gram.name[it as uint]);
            }
        }

        debug!("");
        debug!("rules:");

        let mut line = String::new();
        for i in range(2, gram.nrules) {
            line.push_str(format!("    [r{:-3} ]   {:-10} : ", i, gram.name[gram.rlhs[i] as uint]).as_slice());

            while gram.ritem[k] >= 0 {
                line.push_str(" ");
                line.push_str(gram.name[gram.ritem[k] as uint].as_slice());
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
pub fn read_grammar<'a>(grammar_sp: codemap::Span, parser: &mut Parser /* , tokens_enum: &'a P<ast::Item>, token_variants: &'a [P<ast::Variant>] */ )
    -> (Grammar, Vec<Option<P<Block>>>, Vec<Option<ast::Ident>>) {

    let mut reader: ReaderState = ReaderState::new();

        /*
    // Parse the variants of the "tokens" enum.
    for tv in token_variants.iter() {
        debug!("    token (from enum): {}", tv);
    }
    */

    // create_symbol_table()

    // Add the well-known "error" symbol to the table.
    {
        let (_, bp) = reader.lookup_ref_mut("error", grammar_sp);
        bp.class = SymClass::Terminal;
    }

    // read_declarations();

    // now begins what was read_grammar();


    // first, parse all tokens.

    // let t_token = Token::Ident(Ident("token"), IdentStyle::Plain);

    let mut goal_symbol: Option<uint> = None;

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

                // debug!("ident: id='{}'", id.as_str());
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
                                    assert!(reader.rule_blocks.len() == reader.gram.nrules);
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
                                    debug!("token has value: {}", parser.token);
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
    for i in range(0, reader.symbols.len()) {
        let sym = &reader.symbols[i];
        if sym.class == SymClass::Unknown {
            parser.span_err(sym.span, "symbol was used but never defined");
        }
    }
    parser.abort_if_errors();

    let map_to_packed = reader.pack_symbols(goal_symbol);
    reader.pack_grammar(map_to_packed.as_slice(), goal_symbol);
    ReaderState::print_grammar(&reader.gram);

    (reader.gram, reader.rule_blocks, reader.rhs_binding)
}

