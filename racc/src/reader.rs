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

use crate::grammar::Grammar;
use crate::grammar::{TOKEN, UNDEFINED};
use log::debug;
use log::warn;
use proc_macro2::Span;
use std::collections::HashMap;
use std::mem::replace;
use std::rc::Rc;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{Block, Ident, Token, Type};

const PREDEFINED_RULES: usize = 3;
const PREDEFINED_ITEMS: usize = 4;

const NO_SYMBOL: usize = !0;
const NO_ITEM: usize = !0;

// symbol classes
#[derive(Clone, Copy, PartialEq, Debug)]
enum SymClass {
    Unknown = 0,
    Terminal = 1,
    NonTerminal = 2,
}

struct Symbol {
    name: Ident,
    tag: Option<Rc<String>>,
    // value: i16,
    prec: i16,
    class: SymClass,
    assoc: u8,
}

fn make_symbol(name: Ident) -> Symbol {
    Symbol {
        name: name,
        tag: None,
        // value: UNDEFINED,
        prec: 0,
        class: SymClass::Unknown,
        assoc: TOKEN,
    }
}

struct ReaderState {
    /// Contains indices that point into `self.symbols`, or `NO_ITEM`.
    pitem: Vec<usize>,

    /// Contains indices that point into `self.symbols`, or `NO_SYMBOL`.
    /// len = nrules
    lhs: Vec<usize>,

    /// Contains all of the symbols, in the order that they are first encountered.
    symbols: Vec<Symbol>,

    /// A lookup table, which gives you an index into self.symbols
    symbol_table: HashMap<String, usize>,

    // used for generating names for anonymous symbols
    gensym: u32,

    last_was_action: bool,

    /// rule_precedence
    /// len = nrules
    rprec: Vec<i16>,

    /// rule_associativity
    /// len = nrules
    rassoc: Vec<u8>,

    /// The actions (code blocks) provided by the grammar author, if any.
    /// index = rule index
    /// len = nrules
    rule_blocks: Vec<Option<syn::Block>>,

    /// identifier used by grammar for a RHS value, given by =foo
    /// indices are same as rrhs
    rhs_binding: Vec<Option<Ident>>,
}

impl ReaderState {
    /// Returns number of items defined
    pub fn nitems(&self) -> usize {
        self.pitem.len()
    }

    /// number of rules (productions) in the grammar
    pub fn nrules(&self) -> usize {
        self.lhs.len()
    }

    pub fn new() -> ReaderState {
        ReaderState {
            pitem: vec![NO_ITEM; PREDEFINED_ITEMS],
            lhs: vec![NO_ITEM; PREDEFINED_RULES],
            rule_blocks: vec![None; PREDEFINED_RULES],
            rhs_binding: vec![None; PREDEFINED_ITEMS],
            symbols: Vec::new(),
            symbol_table: HashMap::new(),
            gensym: 1,
            last_was_action: false,
            rprec: vec![0; PREDEFINED_RULES],
            rassoc: vec![TOKEN; PREDEFINED_RULES],
        }
    }

    // Looks up a symbol in the symbol table, and returns the symbol index
    // (the index within ReaderState.symbols) of that symbol.  If the symbol
    // is not already in the symbol table, then this method adds the symbol.
    pub fn lookup(&mut self, name: &Ident) -> usize {
        if let Some(ii) = self.symbol_table.get(&name.to_string()) {
            // debug!("found {}_{} already in table", name, *ii);
            return *ii;
        }

        let index = self.symbols.len();
        let s = make_symbol(name.clone());
        self.symbols.push(s);
        self.symbol_table.insert(name.to_string(), index);
        // debug!("added {}_{} to table", name, index);
        return index;
    }

    pub fn lookup_ref_mut<'a>(&'a mut self, name: &Ident) -> (usize, &'a mut Symbol) {
        let index = self.lookup(name);
        (index, &mut self.symbols[index])
    }

    pub fn start_rule(&mut self, lhs: usize) {
        assert!(self.symbols[lhs].class == SymClass::NonTerminal);

        // debug!("  start_rule: r{}: {}_{} -> (at item {}) ...", self.nrules, self.symbols[lhs].name, lhs, self.pitem.len());

        self.lhs.push(lhs);
        self.rprec.push(UNDEFINED);
        self.rassoc.push(TOKEN);

        // nrules is not yet advanced; that happens in end_rule
    }

    // Terminates the current rule.
    pub fn end_rule(&mut self) {
        assert!(self.nrules() > 0);
        let rule = self.nrules() - 1;

        assert!(self.lhs.len() == self.nrules());
        assert!(self.rprec.len() == self.nrules());
        assert!(self.rassoc.len() == self.nrules());

        if !self.last_was_action && self.symbols[self.lhs[rule]].tag.is_some() {
            if self.pitem[self.pitem.len() - 1] != NO_ITEM {
                let mut i: usize = self.pitem.len() - 1;
                while (i > 0) && self.pitem[i] != NO_ITEM {
                    i -= 1;
                }
                if self.pitem[i + 1] == NO_ITEM
                    || self.symbols[self.pitem[i + 1]].tag != self.symbols[self.lhs[rule]].tag
                {
                    warn!("default_action_warning();")
                }
            }
        }

        // Insert a None entry into rule_blocks, if the current rule did not declare an action.
        if !self.last_was_action {
            self.rule_blocks.push(None);
        }
        self.last_was_action = false;

        self.pitem.push(NO_ITEM);
        self.rhs_binding.push(None);

        assert_eq!(self.rule_blocks.len(), self.nrules());

        // debug!("  end_rule: r{}, lhs={} nitems={}", rule, self.plhs[rule], self.pitem.len());
    }

    /// Adds a new "empty" rule.  A new symbol name is generated, using the pattern $$nn,
    /// where $$ is the literal string "$$" and nn is a number.
    pub fn insert_empty_rule(&mut self, span: Span) {
        self.gensym += 1;
        let symname = format!("__gen_{}", self.gensym); // was "$${}"
        let symname_ident = Ident::new(&symname, span);

        debug!("insert_empty_rule: added symbol {}", symname);

        let rule = self.nrules() - 1;

        let tag: Option<Rc<String>> = self.symbols[self.lhs[rule]].tag.clone();
        let sym_index = {
            let (sym_index, sym) = self.lookup_ref_mut(&symname_ident);
            sym.tag = tag;
            sym.class = SymClass::NonTerminal;
            sym_index
        };

        let mut bpp = self.pitem.len();
        self.pitem.push(NO_ITEM);
        self.pitem.push(sym_index);

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
        self.lhs.insert(rule, sym_index);
        self.rprec.insert(rule, 0);
        self.rassoc.insert(rule, TOKEN);
    }

    /// Adds a symbol to the RHS of the current rule being built.
    /// Can only be called between calls to start_rule() and end_rule().
    pub fn add_symbol(&mut self, bp: usize, span: Span, ident: Option<syn::Ident>) {
        assert!(self.rhs_binding.len() == self.nitems());

        if self.last_was_action {
            // If we have encountered a new rhs symbol for the current rule, and immediately
            // prior to this we encountered an action (a code block), then we need to finish
            // this rule, and rewrite the lhs of this rule to produce a new, anonymous lhs
            // non-terminal.  Then we will start a new rule, using the lhs that we were
            // previously using, with one rhs symbol, which is the generated symbol.
            self.insert_empty_rule(span);
            self.last_was_action = false;
        }

        // debug!("    add_symbol: pitem[{}] = {}_{}", self.pitem.len(), self.symbols[bp].name, bp);

        self.pitem.push(bp);
        self.rhs_binding.push(ident);
    }

    /// "Packs" the symbol table and the grammar definition.  In the packed form, the
    /// tokens are numbered sequentially, and are followed by the non-terminals.
    pub fn pack_symbols_and_grammar(&mut self, goal_symbol: usize) -> Grammar {
        debug!("pack_symbols");

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

        // Build the 'v' table, which maps from packed symbols to unpacked symbols.  The size of the
        // v table is the number of packed symbols (nsyms), which is not the same as the number of
        // unpacked symbols.  This is because the $accept and error symbols are not symbols in the
        // unpacked view.  In u = v[p], p is a packed symbol index (a number in the nsyms space),
        // while u is the unpacked symbol.
        let v = {
            let mut v: Vec<usize> = vec![NO_SYMBOL; nsyms]; // symbol indices, which point into reader.symbols[]
            v[0] = NO_SYMBOL; // $end
            v[start_symbol] = NO_SYMBOL; // $accept

            let mut i: usize = 1; // packed index for assigning tokens
            let mut j: usize = start_symbol + 1; // packed index for assigning vars

            for s in 0..self.symbols.len() {
                match self.symbols[s].class {
                    SymClass::Terminal => {
                        v[i] = s;
                        i += 1;
                    }
                    SymClass::NonTerminal => {
                        v[j] = s;
                        j += 1;
                    }
                    SymClass::Unknown => {
                        panic!("symbol {} has no defined class", self.symbols[s].name);
                    }
                }
            }
            assert_eq!(i, ntokens);
            assert_eq!(j, nsyms);

            for s in 1..v.len() {
                assert!(s == start_symbol || v[s] != NO_SYMBOL);
            }
            v
        };

        // Build the remap table.  map_to_packed[old] gives the index of the packed location.
        // This replaces the bucket::index field, from C.  This is the inverse of v.  The "error"
        // symbol is always at packed index 1.
        let map_to_packed: Vec<i16> = {
            let mut map_to_packed: Vec<i16> = vec![-1; nsyms];
            map_to_packed[0] = 1; // The 'error' symbol
            for i in 1..ntokens {
                map_to_packed[v[i]] = i as i16;
            }
            map_to_packed[goal_symbol] = (start_symbol + 1) as i16;
            let mut k = start_symbol + 2;
            for &s in v[ntokens + 1..nsyms].iter() {
                if s != goal_symbol {
                    map_to_packed[s] = k as i16;
                    k += 1;
                }
            }
            map_to_packed
        };

        let mut gram_name: Vec<Option<Ident>> = vec![None; nsyms];
        let mut gram_value: Vec<i16> = vec![0; nsyms];
        let mut gram_prec: Vec<i16> = vec![0; nsyms];
        let mut gram_assoc: Vec<u8> = vec![0; nsyms];
        let mut gram_rprec = replace(&mut self.rprec, Vec::new());
        let mut gram_rassoc = replace(&mut self.rassoc, Vec::new());

        // symbols_value replaces the bucket::value field.  that is, for (i, j),
        // self.symbols[i].value = j ==> symbols_value[i] = j
        let symbols_value = {
            let mut symbols_value: Vec<i16> = vec![UNDEFINED; self.symbols.len()];
            symbols_value[goal_symbol] = 0;
            let mut k: usize = 1;
            for i in start_symbol + 1..nsyms {
                if v[i] != goal_symbol {
                    symbols_value[v[i]] = k as i16;
                    k += 1;
                }
            }

            // Assign token values
            let mut k = 0;
            for i in 1..ntokens {
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
            for i in 2..ntokens {
                if symbols_value[v[i]] == UNDEFINED {
                    while j < k && n == gram_value[j] {
                        while {
                            j += 1;
                            j < k && n == gram_value[j]
                        } {
                            continue;
                        }
                        n += 1;
                    }
                    symbols_value[v[i]] = n as i16;
                    n += 1;
                }
            }
            symbols_value
        };

        // Propagate $end token
        gram_name[0] = Some(Ident::new("__end", Span::call_site()));
        gram_value[0] = 0;
        gram_prec[0] = 0;
        gram_assoc[0] = TOKEN;

        // Propagate token symbols
        for i in 1..ntokens {
            let from = &self.symbols[v[i]];
            gram_name[i] = Some(from.name.clone());
            gram_value[i] = symbols_value[v[i]];
            gram_prec[i] = from.prec;
            gram_assoc[i] = from.assoc;
        }

        // Set up the start (accept) symbol
        assert!(start_symbol == ntokens);
        gram_name[start_symbol] = Some(Ident::new("__accept", Span::call_site()));
        gram_value[start_symbol] = -1;
        gram_prec[start_symbol] = 0;
        gram_assoc[start_symbol] = TOKEN;

        // Propagate non-terminal symbols
        for i in start_symbol + 1..nsyms {
            let k = map_to_packed[v[i]] as usize;
            assert!(k != NO_SYMBOL);
            let from = &self.symbols[v[i]];
            gram_name[k] = Some(from.name.clone());
            gram_value[k] = symbols_value[v[i]];
            gram_prec[k] = from.prec;
            gram_assoc[k] = from.assoc;
        }

        debug!("packed symbol table:");
        for i in 0..nsyms {
            debug!(
                "    {:3} {} {:20} value {:3} prec {:2} assoc {:2}",
                i,
                if i < ntokens { "token" } else { "var  " },
                gram_name[i].as_ref().unwrap(),
                gram_value[i],
                gram_prec[i],
                gram_assoc[i]
            );
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

        let nrules = self.nrules();

        // there are three pre-defined rules:
        //      -1 -> (nothing)
        //      -1 ->
        //      $accept -> start_symbol

        // Build  rlhs
        let mut rlhs: Vec<i16> = vec![0, 0, start_symbol as i16];
        rlhs.extend(
            self.lhs[PREDEFINED_RULES..nrules]
                .iter()
                .map(|&lhs| map_to_packed[lhs] as i16),
        );

        let mut ritem: Vec<i16> = vec![0; self.nitems()];
        ritem[0] = -1;
        ritem[1] = map_to_packed[goal_symbol];
        ritem[2] = 0;
        ritem[3] = -2;

        let mut rrhs: Vec<i16> = vec![0; nrules + 1];
        rrhs[0] = 0;
        rrhs[1] = 0;
        rrhs[2] = 1;

        let mut j = PREDEFINED_ITEMS; // index of next item to output
        let pitem = &self.pitem;
        let symbols = &self.symbols;
        for i in PREDEFINED_RULES..nrules {
            rrhs[i] = j as i16;
            let mut assoc = TOKEN;
            let mut prec2 = 0u8;
            while pitem[j] != NO_ITEM {
                if symbols[pitem[j]].class == SymClass::Terminal {
                    prec2 = symbols[pitem[j]].prec as u8;
                    assoc = symbols[pitem[j]].assoc;
                }
                ritem[j] = map_to_packed[pitem[j]];
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

            name: gram_name.into_iter().map(|opt| opt.unwrap()).collect(),
            pname: Vec::new(),
            value: gram_value,

            prec: gram_prec,
            assoc: gram_assoc,

            nrules: nrules,

            ritem: ritem,
            rlhs: rlhs,
            rrhs: rrhs,
            rprec: gram_rprec,
            rassoc: gram_rassoc,
        }
    }

    pub fn print_grammar(gram: &Grammar) {
        debug!(
            "symbols: ntokens={} nvars={} nsyms={}",
            gram.ntokens, gram.nvars, gram.nsyms
        );
        for i in 0..gram.nsyms {
            if gram.is_var(i as i16) {
                debug!("    {:3}  var    {}", i, gram.name[i]);
            } else {
                debug!("    {:3}  token  {}", i, gram.name[i]);
            }
        }
        debug!("");
        debug!("raw items:");

        for i in 0..gram.ritem.len() {
            let it = gram.ritem[i];
            if it < 0 {
                debug!("    {:3} --> {:3}", i, it);
            } else {
                debug!("    {:3} --> {:3} {}", i, it, gram.name[it as usize]);
            }
        }

        debug!("");
        debug!("rules:");

        let mut k: usize = 1;
        let mut line = String::new();
        for i in 2..gram.nrules {
            line.push_str(&format!(
                "    [r{:-3} ]   {:-10} : ",
                i, gram.name[gram.rlhs[i] as usize]
            ));
            while gram.ritem[k] >= 0 {
                line.push_str(&format!(" {}", gram.name[gram.ritem[k] as usize]));
                k += 1;
            }
            k += 1;

            debug!("{}", line);
            line.clear();
        }

        debug!("");
    }
}

pub struct Grammar2 {
    pub grammar: Grammar,
    pub app_context_ty: Type,
    pub value_ty: Type,
    pub rule_blocks: Vec<Option<Block>>,
    pub rhs_bindings: Vec<Option<Ident>>,
}

impl Parse for Grammar2 {
    fn parse(input: ParseStream<'_>) -> syn::Result<Grammar2> {
        let mut reader: ReaderState = ReaderState::new();

        use syn::parse_quote;

        let app_context_ty: Type = parse_quote! { AppContext };
        let value_ty: Type = parse_quote! { Option<i16> };

        // Add the well-known "error" symbol to the table.
        {
            let (_, s) = reader.lookup_ref_mut(&Ident::new("error", Span::call_site()));
            s.class = SymClass::Terminal;
        }

        // first, parse all tokens.

        let mut goal_symbol: Option<usize> = None;

        // debug!("parsing token definitions");
        while !input.is_empty() {
            // println!("racc: parsing rule");

            // debug!("token: {:?}", la);
            let la = input.lookahead1();
            if la.peek(Ident) {
                // An identifier can start either a token definition or a rule definition.
                // The next character will tell us whether this is a token definition or a
                // rule definition.
                //      : (begins a rule)
                //      = (defines a token with a specific value)
                //      ; (defines a token with an automatically-assigned value)
                let id = input.parse::<Ident>()?;
                let name_def_str = id.to_string();
                let name_def_span = id.span();
                let lhs = reader.lookup(&id);
                // println!("- id: {}", name_def_str);

                let la = input.lookahead1();
                if la.peek(syn::token::Colon) {
                    // debug!("found ':', beginning a rule");
                    input.parse::<syn::token::Colon>()?;
                    match reader.symbols[lhs].class {
                        SymClass::Terminal => {
                            return Err(syn::Error::new(name_def_span, "name has been defined as a token, and so cannot be on the left-hand side of a rule"));
                            // parser.span_err(reader.symbols[lhs].span, "see definition of token");
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

                    reader.start_rule(lhs);

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
                        let la = input.lookahead1();
                        if la.peek(Ident) {
                            let rhs_ident = input.parse::<Ident>()?;
                            // debug!("rule: found token/symbol ref '{}'", rhs_name);
                            let rhs = reader.lookup(&rhs_ident);

                            // see if the symbol is followed by "= binding".
                            let mut rbind: Option<Ident> = None;
                            if input.lookahead1().peek(syn::token::Eq) {
                                input.parse::<syn::token::Eq>()?;
                                let la = input.lookahead1();
                                if la.peek(Ident) {
                                    // debug!("found rhs binding");
                                    let rhs_bind_ident = input.parse()?;
                                    rbind = Some(rhs_bind_ident);
                                } else {
                                    return Err(la.error());
                                }
                            }
                            reader.add_symbol(rhs, rhs_ident.span(), rbind);
                        } else if la.peek(syn::token::Or) {
                            input.parse::<syn::token::Or>()?;
                            reader.end_rule();
                            reader.start_rule(lhs);
                        } else if la.peek(syn::token::Brace) {
                            let block = input.parse::<syn::Block>()?;
                            // Parse an action (a code block).  Parsing it is actually very easy, thanks to Rust!
                            // assert!(reader.rule_blocks.len() == reader.nrules);
                            if reader.last_was_action {
                                reader.insert_empty_rule(block.span());
                            }
                            reader.rule_blocks.push(Some(block));
                            reader.last_was_action = true;
                        } else if la.peek(Token![;]) {
                            input.parse::<Token![;]>()?;
                            reader.end_rule();
                            break;
                        } else {
                            return Err(la.error());
                        }
                    }
                } else if la.peek(Token![=]) || la.peek(Token![;]) {
                    let has_value = la.peek(Token![=]);
                    if la.peek(syn::token::Eq) {
                        input.parse::<Token![=]>()?;
                    } else {
                        input.parse::<Token![;]>()?;
                    }

                    match reader.symbols[lhs].class {
                        SymClass::Terminal => {
                            // symbol class is already known, but this means user has defined same symbol twice
                            return Err(syn::Error::new(
                                name_def_span,
                                "token is defined more than once",
                            ));
                            // parser.span_err(reader.symbols[lhs].span, "location of previous definition");
                        }
                        SymClass::NonTerminal => {
                            // this name is defined inconsistently -- as both a variable and a token
                            return Err(syn::Error::new(
                                name_def_span,
                                "token was previously used as a variable",
                            ));
                            // parser.span_err(reader.symbols[lhs].span, "location of previous definition");
                        }
                        SymClass::Unknown => {
                            // debug!("resolving forward ref of a token '{}'", name_def_str);
                            reader.symbols[lhs].class = SymClass::Terminal;
                        }
                    }

                    // debug!("defining token '{}' at unpacked symbol index {}", name_def_str, lhs);

                    if has_value {
                        let la = input.lookahead1();
                        if la.peek(syn::Lit) {
                            let _lit: syn::Lit = input.parse()?;
                            // debug!("token has value: {:?}", lit);
                            let la = input.lookahead1();
                            if la.peek(Token![;]) {
                                input.parse::<Token![;]>()?;
                            } else {
                                return Err(la.error());
                            }
                        } else {
                            return Err(la.error());
                        }
                    }
                } else {
                    return Err(la.error());
                }
            } else {
                return Err(la.error());
            }
        }

        debug!("");

        // Check that we found a goal state.  This check was in check_symbols().
        // Rebind 'goal_symbol' now that we know it exists.
        let goal_symbol = if let Some(goal) = goal_symbol {
            goal
        } else {
            return Err(input.error("grammar does not define any rules"));
        };
        debug!(
            "goal symbol = {}_{}",
            reader.symbols[goal_symbol].name, goal_symbol
        );

        // Check for any symbols that were not defined.
        for i in 0..reader.symbols.len() {
            let sym = &reader.symbols[i];
            if sym.class == SymClass::Unknown {
                return Err(syn::Error::new(
                    sym.name.span(),
                    "symbol was used but never defined",
                ));
            }
        }
        //    parser.abort_if_errors();

        let gram = reader.pack_symbols_and_grammar(goal_symbol);
        ReaderState::print_grammar(&gram);

        // -> (Grammar, Vec<Option<Expr>>, Vec<Option<syn::Ident>>)

        // println!("finished parsing grammar");

        Ok(Grammar2 {
            grammar: gram,
            rule_blocks: reader.rule_blocks,
            rhs_bindings: reader.rhs_binding,
            app_context_ty,
            value_ty,
        })
    }
}
