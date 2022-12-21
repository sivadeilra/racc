//! Reads a sequence of Rust tokens, which are provided in the body of a macro invocation,
//! and builds a Grammar.
//!
//! Our grammar for a grammar:
//!
//! ```ignore
//! <ident> : <ident> ... | <ident> ... ;    // rule def
//! <ident> [ = <literal> ];                 // token def, must precede all rule defs
//! ```
//!
//! This module reads a sequence of input tokens and builds a YACC grammar.
//! It builds a symbol table (names), which name both tokens and variables of the
//! defined grammar.  It also builds the rules of the grammar.  Rules are represented
//! as a table of left-hand side symbols (the plhs vector) and a table of right-hand
//! side symbols (the ritem vector).  The rhs symbols for all rules are packed into
//! a single array, the ritem vector.  Each sequence of rhs symbols (for a single rule)
//! are stored sequentially, and each rule is terminated by a NO_ITEM symbol.
//!
//! As the grammar is parsed, we build a name table.  The name table associates an
//! integer with each name, which is an index into the ReaderState.symbols table.
//! Other tables, such as plhs and ritem, contain indices into the symbols table.
//!
//! Because indices are added in the order that they are found in the grammar,
//! tokens and variables are mixed together in this table.  After the grammar is
//! parsed, it is "packed".  This produces a new table, which lists all tokens,
//! then all variables.  The plhs and ritem tables are read, and are used to
//! produce several new tables.
//!
//! This module is a port of the original Berkeley YACC code. Although RACC and YACC
//! are quite different syntactically, the algorithms and (at a certain level of
//! abstraction) the data structures are quite similar.
//!
use super::*;
use crate::grammar::Grammar;
use crate::grammar::UNDEFINED;
use crate::Rule;
use crate::SymbolOrRule;
use crate::{Item, Symbol};
use log::debug;
use log::warn;
use proc_macro2::Span;
use std::collections::HashMap;
use std::rc::Rc;
use syn::parse_quote;
use syn::spanned::Spanned;
use syn::{Ident, Token, Type};

const PREDEFINED_RULES: usize = 3;
const PREDEFINED_ITEMS: usize = 4;

const NO_SYMBOL: usize = !0;
const NO_ITEM: usize = !0;

// symbol classes
#[derive(Clone, Copy, PartialEq, Debug)]
enum SymClass {
    Unknown,
    Terminal,
    NonTerminal,
}

struct SymbolDef {
    name: Ident,
    tag: Option<Rc<String>>,
    prec: i16,
    class: SymClass,
    assoc: Assoc,
    /// If Some, then this gives the span of where the assoc/prec was specified.
    assoc_prec_specified: Option<Span>,
    value_type: Option<syn::Type>,
}

fn make_symbol(name: Ident) -> SymbolDef {
    SymbolDef {
        name,
        tag: None,
        prec: 0,
        class: SymClass::Unknown,
        assoc: Assoc::TOKEN,
        assoc_prec_specified: None,
        value_type: None,
    }
}

/// Contains state used while parsing the input grammar.
struct ReaderState {
    /// Contains indices that point into `self.symbols`, or `NO_ITEM`.
    pitem: Vec<usize>,

    /// Contains indices that point into `self.symbols`, or `NO_SYMBOL`.
    /// len = nrules
    lhs: Vec<usize>,

    /// Contains all of the symbols, in the order that they are first encountered.
    symbols: Vec<SymbolDef>,

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
    rassoc: Vec<Assoc>,

    /// The ideal span to use when reporting errors for a rule.
    /// (len = nrules)
    rule_span: Vec<Span>,

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

    pub fn new() -> Self {
        Self {
            pitem: vec![NO_ITEM; PREDEFINED_ITEMS],
            lhs: vec![NO_ITEM; PREDEFINED_RULES],
            rule_blocks: vec![None; PREDEFINED_RULES],
            rule_span: vec![Span::call_site(); PREDEFINED_RULES],
            rhs_binding: vec![None; PREDEFINED_ITEMS],
            symbols: Vec::new(),
            symbol_table: HashMap::new(),
            gensym: 1,
            last_was_action: false,
            rprec: vec![0; PREDEFINED_RULES],
            rassoc: vec![Assoc::TOKEN; PREDEFINED_RULES],
        }
    }

    /// Looks up a symbol in the symbol table, and returns the symbol index
    /// (the index within ReaderState.symbols) of that symbol.  If the symbol
    /// is not already in the symbol table, then this method adds the symbol.
    pub fn lookup(&mut self, name: &Ident) -> usize {
        if let Some(ii) = self.symbol_table.get(&name.to_string()) {
            return *ii;
        }

        let index = self.symbols.len();
        let symbol = make_symbol(name.clone());
        self.symbols.push(symbol);
        self.symbol_table.insert(name.to_string(), index);
        index
    }

    pub fn lookup_ref_mut<'a>(&'a mut self, name: &Ident) -> (usize, &'a mut SymbolDef) {
        let index = self.lookup(name);
        (index, &mut self.symbols[index])
    }

    pub fn start_rule(&mut self, lhs: usize, span: Span) {
        assert_eq!(self.nrules(), self.rule_span.len(), "start of start_rule");

        assert!(self.symbols[lhs].class == SymClass::NonTerminal);
        self.lhs.push(lhs);
        self.rprec.push(UNDEFINED);
        self.rassoc.push(Assoc::TOKEN);
        self.rule_span.push(span);

        assert_eq!(self.nrules(), self.rule_span.len(), "end of start_rule");
    }

    // Terminates the current rule.
    pub fn end_rule(&mut self, _span: Span) {
        assert!(self.nrules() > 0);
        let rule = self.nrules() - 1;

        assert!(self.lhs.len() == self.nrules());
        assert!(self.rprec.len() == self.nrules());
        assert!(self.rassoc.len() == self.nrules());

        if !self.last_was_action
            && self.symbols[self.lhs[rule]].tag.is_some()
            && self.pitem[self.pitem.len() - 1] != NO_ITEM
        {
            let mut i = self.pitem.len() - 1;
            while i > 0 && self.pitem[i] != NO_ITEM {
                i -= 1;
            }
            if self.pitem[i + 1] == NO_ITEM
                || self.symbols[self.pitem[i + 1]].tag != self.symbols[self.lhs[rule]].tag
            {
                warn!("default_action_warning();")
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
        assert_eq!(
            self.rule_span.len(),
            self.nrules(),
            "rule_span has wrong len, in end_rule"
        );
    }

    /// Adds a new "empty" rule.  A new symbol name is generated, using the pattern "__gen_{}",
    /// where "{}" is a number that is incremented for each empty rule.
    pub fn insert_empty_rule(&mut self, span: Span) {
        self.gensym += 1;
        let symname = format!("__gen_{}", self.gensym); // was "$${}"
        let symname_ident = Ident::new(&symname, span);

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
        self.rhs_binding.push(None);
        self.rhs_binding.push(None);

        loop {
            let b = self.pitem[bpp - 1];
            self.pitem[bpp] = b;

            let bi = self.rhs_binding[bpp - 1].take();
            self.rhs_binding[bpp] = bi;

            if b == NO_ITEM {
                break;
            }
            bpp -= 1;
        }

        // Insert the generated rule right before the current rule, which was
        // written to self.{plhs,rprec,rassoc}[nrules].
        self.lhs.insert(rule, sym_index);
        self.rprec.insert(rule, 0);
        self.rassoc.insert(rule, Assoc::TOKEN);
        self.rule_span.insert(rule, span); // TODO: not sure about this
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

        self.pitem.push(bp);
        self.rhs_binding.push(ident);
    }

    /// "Packs" the symbol table and the grammar definition.  In the packed form, the
    /// tokens are numbered sequentially, and are followed by the non-terminals.
    fn pack_symbols_and_grammar(
        self,
        goal_symbol: usize,
        context_ty: Option<syn::Type>,
    ) -> Grammar {
        debug!("pack_symbols");

        assert!(goal_symbol < self.symbols.len());
        assert!(self.symbols[goal_symbol].class == SymClass::NonTerminal);

        let nsyms: usize = 2 + self.symbols.len(); // $end and $accept
        let mut ntokens: usize = 1; // $end

        // Count the number of tokens.
        for sym in self.symbols.iter() {
            if matches!(sym.class, SymClass::Terminal | SymClass::Unknown) {
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
                        // We can only get here if a previous error occured.
                        // We're trying to get as far as we can, so we can report as many
                        // useful errors to the user. Treat this like a Terminal, for now.
                        v[i] = s;
                        i += 1;
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
        let map_to_packed: Vec<Symbol> = {
            let mut map_to_packed: Vec<Symbol> = vec![Symbol(-1); nsyms];
            map_to_packed[0] = Symbol::ERROR; // The 'error' symbol
            for i in 1..ntokens {
                map_to_packed[v[i]] = Symbol(i as i16);
            }
            map_to_packed[goal_symbol] = Symbol((start_symbol + 1) as i16);
            let mut k = start_symbol + 2;
            for &s in v[ntokens + 1..nsyms].iter() {
                if s != goal_symbol {
                    map_to_packed[s] = Symbol(k as i16);
                    k += 1;
                }
            }
            map_to_packed
        };

        let mut gram_name: Vec<Ident> = Vec::with_capacity(nsyms);
        let mut gram_value: Vec<i16> = vec![0; nsyms];
        let mut gram_prec: Vec<i16> = Vec::with_capacity(nsyms);
        let mut gram_assoc: Vec<Assoc> = Vec::with_capacity(nsyms);
        let mut gram_sym_type: Vec<Option<syn::Type>> = Vec::with_capacity(nsyms);
        let mut gram_rprec = self.rprec.clone();
        let mut gram_rassoc = self.rassoc.clone();

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
                    gram_value[j] = n;
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
                    symbols_value[v[i]] = n;
                    n += 1;
                }
            }
            symbols_value
        };

        // Propagate $end token
        gram_name.push(Ident::new("__end", Span::call_site()));
        gram_sym_type.push(None);
        gram_value[0] = 0;
        gram_prec.push(0);
        gram_assoc.push(Assoc::TOKEN);

        // Propagate token symbols
        for i in 1..ntokens {
            let from = &self.symbols[v[i]];
            gram_name.push(from.name.clone());
            gram_sym_type.push(from.value_type.clone());
            gram_value[i] = symbols_value[v[i]];
            gram_prec.push(from.prec);
            gram_assoc.push(from.assoc);
        }

        // Set up the start (accept) symbol
        assert!(start_symbol == ntokens);
        gram_name.push(Ident::new("__accept", Span::call_site()));
        gram_sym_type.push(None); // TODO: need to get this from the grammar
        gram_value[start_symbol] = -1;
        gram_prec.push(0);
        gram_assoc.push(Assoc::TOKEN);

        // Propagate non-terminal symbols
        for i in start_symbol + 1..nsyms {
            let from = &self.symbols[v[i]];
            gram_name.push(from.name.clone());
            gram_sym_type.push(from.value_type.clone());
            gram_value[i] = symbols_value[v[i]];
            gram_prec.push(from.prec);
            gram_assoc.push(from.assoc);
        }

        assert_eq!(gram_name.len(), nsyms);
        assert_eq!(gram_prec.len(), nsyms);
        assert_eq!(gram_assoc.len(), nsyms);

        debug!("packed symbol table:");
        for i in 0..nsyms {
            debug!(
                "    {:3} {} {:20} value {:3} prec {:2} assoc {:2?}",
                i,
                if i < ntokens { "token" } else { "var  " },
                gram_name[i],
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
        let mut rlhs: Vec<Symbol> = vec![Symbol(0), Symbol(0), Symbol(start_symbol as i16)];
        rlhs.extend(
            self.lhs[PREDEFINED_RULES..nrules]
                .iter()
                .map(|&lhs| map_to_packed[lhs]),
        );

        let mut ritem: Vec<SymbolOrRule> = vec![SymbolOrRule::symbol(Symbol::NULL); self.nitems()];
        ritem[0] = SymbolOrRule::rule(Rule::RULE_1);
        ritem[1] = SymbolOrRule::symbol(map_to_packed[goal_symbol]);
        ritem[2] = SymbolOrRule::symbol(Symbol::NULL);
        ritem[3] = SymbolOrRule::rule(Rule::RULE_2);

        let mut rrhs: Vec<Item> = Vec::with_capacity(nrules + 1);
        rrhs.push(Item::NULL);
        rrhs.push(Item::NULL);
        rrhs.push(Item(1));

        let mut j = PREDEFINED_ITEMS; // index of next item to output
        let pitem = &self.pitem;
        let symbols = &self.symbols;
        for i in PREDEFINED_RULES..nrules {
            rrhs.push(Item(j as i16));
            let mut assoc = Assoc::TOKEN;
            let mut prec2: i16 = 0;
            while pitem[j] != NO_ITEM {
                if symbols[pitem[j]].class == SymClass::Terminal {
                    prec2 = symbols[pitem[j]].prec;
                    assoc = symbols[pitem[j]].assoc;
                }
                ritem[j] = SymbolOrRule::symbol(map_to_packed[pitem[j]]);
                j += 1;
            }

            // Terminate the item list with the negative of the rule index.
            // This is important; it is used by the code in lr0::save_reductions()
            // in order to realize when we've reached the end of a rule, and so can
            // emit a reduction in a particular state.
            ritem[j] = SymbolOrRule::rule(Rule(i as i16));
            j += 1;
            if gram_rprec[i] == UNDEFINED {
                gram_rprec[i] = prec2;
                gram_rassoc[i] = assoc;
            }
        }

        // Terminate the rrhs list
        rrhs.push(Item(j as i16));

        assert_eq!(nrules, rlhs.len(), "blar");

        assert_eq!(
            nrules,
            self.rule_span.len(),
            "rule_span.len() is wrong, at end"
        );
        assert_eq!(nrules, self.rule_blocks.len());

        Grammar {
            nsyms,
            ntokens,
            nvars,
            name: gram_name,
            value: gram_value,
            prec: gram_prec,
            assoc: gram_assoc,
            sym_type: gram_sym_type,
            nrules,
            ritem,
            rlhs,
            rrhs,
            rprec: gram_rprec,
            rassoc: gram_rassoc,
            rule_span: self.rule_span,
            rhs_binding: self.rhs_binding,
            rule_blocks: self.rule_blocks,
            context_ty,
        }
    }

    pub fn print_grammar(gram: &Grammar) {
        debug!(
            "symbols: ntokens={} nvars={} nsyms={}",
            gram.ntokens, gram.nvars, gram.nsyms
        );
        for i in 0..gram.nsyms {
            if gram.is_var(Symbol(i as i16)) {
                debug!("    {:3}  var    {}", i, gram.name[i]);
            } else {
                debug!("    {:3}  token  {}", i, gram.name[i]);
            }
        }
        debug!("");
        debug!("raw items:");

        for i in 0..gram.ritem.len() {
            let it = gram.ritem[i];
            if it.is_rule() {
                debug!("    {:3} --> r{:3}", i, it.as_rule());
            } else {
                debug!(
                    "    {:3} --> {:3} {}",
                    i,
                    it.as_symbol().0,
                    gram.name[it.as_symbol().0 as usize]
                );
            }
        }

        debug!("");
        debug!("rules:");

        let mut k: usize = 1;
        let mut line = String::new();
        for i in 2..gram.nrules {
            line.push_str(&format!(
                "    [r{:-3} ]   {:-10} : ",
                i, gram.name[gram.rlhs[i].0 as usize]
            ));
            while gram.ritem[k].is_symbol() {
                line.push_str(&format!(" {}", gram.name(gram.ritem[k].as_symbol())));
                k += 1;
            }
            k += 1;

            debug!("{}", line);
            line.clear();
        }

        debug!("");
    }
}

#[derive(Default)]
pub(crate) struct Errors {
    pub(crate) errors: Vec<syn::Error>,
}

impl Errors {
    pub(crate) fn push(&mut self, e: syn::Error) {
        self.errors.push(e);
    }

    pub(crate) fn into_result(self) -> Result<(), syn::Error> {
        let mut iter = self.errors.into_iter();
        if let Some(mut errors) = iter.next() {
            for e in iter {
                errors.combine(e);
            }
            Err(errors)
        } else {
            Ok(())
        }
    }

    pub(crate) fn into_token_stream(self) -> TokenStream {
        if self.errors.is_empty() {
            return TokenStream::new();
        }

        let mut t = TokenStream::new();
        for e in self.errors.into_iter() {
            t.extend(e.into_compile_error().into_token_stream());
        }
        t
    }
}

impl Parse for Grammar {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let mut reader: ReaderState = ReaderState::new();
        let mut context_ty: Option<Type> = None;
        let mut errors = Errors::default();

        // Add the well-known "error" symbol to the table.
        {
            let (_, s) = reader.lookup_ref_mut(&Ident::new("error", Span::call_site()));
            s.class = SymClass::Terminal;
        }

        let mut goal_symbol: Option<usize> = None;
        let mut next_left_precedence: i16 = 0;
        let mut next_right_precedence: i16 = 0;

        while !input.is_empty() {
            let la = input.lookahead1();
            if la.peek(Token![type]) {
                // `type Value = <some type>;` - specifies the value stack type.
                input.parse::<Token![type]>()?; // should always succeed
                let keyword = input.parse::<Ident>()?;
                input.parse::<Token![=]>()?;
                let ty = input.parse::<Type>()?;
                input.parse::<Token![;]>()?;

                let keyword_string = keyword.to_string();
                if keyword_string == "Context" {
                    if context_ty.is_some() {
                        errors.push(syn::Error::new(
                            keyword.span(),
                            "The 'Context' type cannot be specified more than once.",
                        ));
                    } else {
                        context_ty = Some(ty);
                    }
                } else {
                    errors.push(syn::Error::new(
                        keyword.span(),
                        format!("The type '{}' is unrecognized.", keyword_string),
                    ));
                }
            } else if la.peek(Ident) {
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

                let mut la = input.lookahead1();

                let mut var_return_type: Option<syn::Type> = None;
                if la.peek(Token![->]) {
                    input.parse::<Token![->]>().unwrap();
                    match input.parse::<syn::Type>() {
                        Ok(t) => var_return_type = Some(t),
                        Err(e) => errors.push(e),
                    }
                    la = input.lookahead1();
                }

                if la.peek(syn::token::Colon) {
                    input.parse::<syn::token::Colon>()?;
                    match reader.symbols[lhs].class {
                        SymClass::Terminal => {
                            errors.push(syn::Error::new(
                                name_def_span,
                                "name has been defined as a token, and so cannot be on the \
                                 left-hand side of a rule",
                            ));
                            // we continue executing, even with a bogus name index.
                        }
                        SymClass::NonTerminal => {
                            // good, this symbol is already known to be a non-terminal
                        }
                        SymClass::Unknown => {
                            reader.symbols[lhs].class = SymClass::NonTerminal;
                        }
                    }

                    if let Some(rt) = var_return_type {
                        let sym_rt = &mut reader.symbols[lhs].value_type;
                        if let Some(existing_rt) = &*sym_rt {
                            errors.push(syn::Error::new(
                                sym_rt.span(),
                                "conflicting definition for type of non-terminal",
                            ));
                            errors.push(syn::Error::new(
                                existing_rt.span(),
                                "conflicting definition for type of non-terminal",
                            ));
                        }

                        *sym_rt = Some(rt);
                    }

                    reader.start_rule(lhs, name_def_span);

                    if goal_symbol.is_none() {
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
                            let rhs = reader.lookup(&rhs_ident);
                            let mut rbind: Option<Ident> = None;

                            // TODO: Remove this, after converting all rhs bindings to use Foo(x).
                            if input.lookahead1().peek(syn::token::Eq) {
                                input.parse::<syn::token::Eq>()?;

                                let la = input.lookahead1();
                                if la.peek(Ident) {
                                    let rhs_bind_ident: Ident = input.parse()?;

                                    errors.push(syn::Error::new(
                                        rhs_bind_ident.span(),
                                        "convert this to the new form",
                                    ));

                                    rbind = Some(rhs_bind_ident);
                                } else {
                                    return Err(la.error());
                                }
                            }

                            // Check to see whether there is a name binding specified after this
                            // variable, using Foo(x) syntax (a tuple pattern after the symbol).
                            if input.lookahead1().peek(syn::token::Paren) {
                                let pat = input.parse::<syn::Pat>()?;
                                // println!("parsed pat");
                                match &pat {
                                    syn::Pat::Tuple(tuple) => {
                                        // println!("it's a tuple, len = {}", tuple.elems.len());
                                        if tuple.elems.len() == 1 {
                                            match &tuple.elems[0] {
                                                syn::Pat::Ident(pat_ident) => {
                                                    // println!("pat_ident = {}", pat_ident.ident);
                                                    rbind = Some(pat_ident.ident.clone());
                                                }
                                                _ => {
                                                    errors.push(syn::Error::new(pat.span(),
                                                    "the pattern must specify exactly one name binding"));
                                                }
                                            }
                                        } else {
                                            errors.push(syn::Error::new(
                                                pat.span(),
                                                "the pattern must specify exactly one name binding",
                                            ));
                                        }
                                    }
                                    _ => {
                                        errors.push(syn::Error::new(
                                            pat.span(),
                                            "the pattern must be a tuple pattern, i.e. `(foo)`",
                                        ));
                                    }
                                }
                            }

                            reader.add_symbol(rhs, rhs_ident.span(), rbind);
                        } else if la.peek(syn::token::Or) {
                            let or_token = input.parse::<syn::token::Or>()?;
                            reader.end_rule(name_def_span);
                            reader.start_rule(lhs, or_token.span());
                        } else if la.peek(syn::token::Brace) {
                            let block: syn::Block = match input.parse::<syn::Block>() {
                                Ok(block) => block,
                                Err(e) => {
                                    errors.push(e);
                                    parse_quote!({ panic!() })
                                }
                            };

                            // Parse an action (a code block).  Parsing it is actually very easy, thanks to Rust!
                            if reader.last_was_action {
                                reader.insert_empty_rule(block.span());
                            }
                            reader.rule_blocks.push(Some(block));
                            reader.last_was_action = true;
                        } else if la.peek(Token![;]) {
                            input.parse::<Token![;]>()?;
                            reader.end_rule(name_def_span);
                            break;
                        } else if la.peek(syn::LitChar) {
                            // Matching character tokens is not fully implemented.
                            let char_token = input.parse::<syn::LitChar>()?;
                            let ch = char_token.value();
                            log::debug!("char_token: {:?}", ch);
                            errors.push(syn::Error::new(
                                char_token.span(),
                                "character tokens are not implemented",
                            ));
                        } else {
                            return Err(la.error());
                        }
                    }
                } else if la.peek(Token![=]) || la.peek(Token![;]) {
                    if let Some(rt) = var_return_type {
                        errors.push(syn::Error::new(
                            rt.span(),
                            "tokens cannot use this syntax for return types",
                        ));
                    }

                    let has_value = la.peek(Token![=]);
                    if la.peek(Token![=]) {
                        input.parse::<Token![=]>()?;
                    } else {
                        input.parse::<Token![;]>()?;
                    }

                    match reader.symbols[lhs].class {
                        SymClass::Terminal => {
                            // symbol class is already known, but this means user has defined same symbol twice
                            errors.push(syn::Error::new(
                                name_def_span,
                                "token is defined more than once",
                            ));
                            // parser.span_err(reader.symbols[lhs].span, "location of previous definition");
                        }
                        SymClass::NonTerminal => {
                            // this name is defined inconsistently -- as both a variable and a token
                            errors.push(syn::Error::new(
                                name_def_span,
                                "token was previously used as a variable",
                            ));
                        }
                        SymClass::Unknown => {
                            reader.symbols[lhs].class = SymClass::Terminal;
                        }
                    }

                    if has_value {
                        let la = input.lookahead1();
                        if la.peek(syn::Lit) {
                            let _lit: syn::Lit = input.parse()?;
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
            } else if la.peek(Token![enum]) {
                let en_ty = input.parse::<syn::ItemEnum>()?;

                if en_ty.ident == "Token" {
                    generics_are_not_allowed_here(&mut errors, &en_ty.generics);
                    attrs_are_not_allowed_here(&mut errors, &en_ty.attrs);

                    for var in en_ty.variants.iter() {
                        // TODO: do something with assoc

                        if let Some(disc) = &var.discriminant {
                            errors.push(syn::Error::new(
                                disc.1.span(),
                                "tokens may not specify a discriminant (vlaue)",
                            ));
                        } else {
                            // The grammar does not define a value for the token.
                            // That's fine, we supply the values.
                        }

                        // TODO: match on #[left] attribute

                        let id = &var.ident;
                        // let name_def_str = id.to_string();
                        // let name_def_span = id.span();
                        let lhs = reader.lookup(id);

                        let sym = &mut reader.symbols[lhs];
                        match sym.class {
                            SymClass::NonTerminal => {
                                errors.push(syn::Error::new(
                                    var.span(),
                                    "This name has a conflicting definition. It is defined as both a token and variable."
                                ));
                                continue;
                            }
                            SymClass::Terminal => {
                                // Hmmm, it was already defined.
                                // That's ok for now, but if we eliminate the old form, this should
                                // become an error.
                            }
                            SymClass::Unknown => {
                                sym.class = SymClass::Terminal;

                                match &var.fields {
                                    syn::Fields::Named(_) => {
                                        errors.push(syn::Error::new(var.fields.span(), "named fields are not supported; use a single-value tuple"));
                                    }

                                    syn::Fields::Unnamed(fields) => {
                                        // This token provides a value. Only a single value is allowed.
                                        if fields.unnamed.len() != 1 {
                                            errors.push(syn::Error::new(
                                                var.fields.span(),
                                                "token enums may only contain a single vlaue",
                                            ));
                                        }

                                        if let Some(f0) = fields.unnamed.first() {
                                            attrs_are_not_allowed_here(&mut errors, &f0.attrs);
                                            sym.value_type = Some(f0.ty.clone());
                                        }
                                    }

                                    syn::Fields::Unit => {
                                        // This token does not have a value.
                                        // The value_type field is already None, so we don't need to do anything.
                                    }
                                }
                            }
                        }
                    }
                } else {
                    errors.push(syn::Error::new(
                        en_ty.ident.span(),
                        "The name of the enum being defined is not recognized. \
                         The only allowed value is 'Token', which defines the set of tokens \
                         defined by your grammar.",
                    ));
                }
            } else if la.peek(Token![%]) {
                // It's a directive, like %left and %right.
                input.parse::<Token![%]>()?;

                let la = input.lookahead1();
                if la.peek(Ident) {
                    let directive: Ident = input.parse::<Ident>()?;

                    let assoc: Assoc;
                    let precedence: i16;
                    if directive == "left" {
                        assoc = Assoc::LEFT;
                        precedence = next_left_precedence;
                        next_left_precedence += 1;
                    } else if directive == "right" {
                        assoc = Assoc::RIGHT;
                        precedence = next_right_precedence;
                        next_right_precedence += 1;
                    } else {
                        return Err(syn::Error::new(directive.span(), "unrecognized directive.  the only valid directives are `%left` and `%right`."));
                    };

                    // Consume identifiers, which are the names of tokens, until we reach ';'.
                    loop {
                        let la = input.lookahead1();
                        if la.peek(Ident) {
                            let token_ident: Ident = input.parse()?;
                            println!("setting token associativity and precedence: {}: assoc {:?} prec {:?}", token_ident, precedence, assoc);

                            // Look up the token. This implicitly creates a new token, if it has
                            // not already been defined.
                            let sym_index = reader.lookup(&token_ident);
                            let sym = &mut reader.symbols[sym_index];

                            match sym.class {
                                SymClass::Unknown => {
                                    errors.push(syn::Error::new(token_ident.span(),
                                        "please define this token before declaring its associativity"));
                                }
                                SymClass::Terminal => {
                                    if let Some(existing_span) = sym.assoc_prec_specified.as_ref() {
                                        errors.push(syn::Error::new(
                                            token_ident.span(),
                                            "the associativity and precedence for this token has already been specified"
                                        ));
                                        errors.push(syn::Error::new(
                                            existing_span.span(),
                                            "location of conflicting definition",
                                        ));
                                    } else {
                                        sym.assoc = assoc;
                                        sym.prec = precedence;
                                        sym.assoc_prec_specified = Some(token_ident.span());
                                    }
                                }
                                SymClass::NonTerminal => {
                                    errors.push(syn::Error::new(token_ident.span(),
                                        "cannot set associativity for non-terminals, only for terminals (tokens)"
                                    ));
                                }
                            }
                        } else if la.peek(Token![;]) {
                            input.parse::<Token![;]>()?;
                            break;
                        } else {
                            return Err(syn::Error::new(
                                input.span(),
                                "expected only token identifiers and a `;` delimiter.",
                            ));
                        }
                    }
                } else {
                    return Err(la.error());
                }
            } else {
                // If we can't recognize the next token at all, then we cannot continue parsing
                // the macro invocation.
                errors.push(la.error());
                break;
            }
        }

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
        for sym in reader.symbols.iter() {
            if sym.class == SymClass::Unknown {
                errors.push(syn::Error::new(
                    sym.name.span(),
                    format!("symbol '{}' was used but never defined", sym.name),
                ));
            }
        }

        let gram = reader.pack_symbols_and_grammar(goal_symbol, context_ty);
        ReaderState::print_grammar(&gram);

        errors.into_result()?;

        Ok(gram)
    }
}

fn attrs_are_not_allowed_here(errors: &mut Errors, attrs: &[syn::Attribute]) {
    for a in attrs.iter() {
        errors.push(syn::Error::new(a.span(), "attributes are not allowed here"));
    }
}

fn generics_are_not_allowed_here(errors: &mut Errors, generics: &syn::Generics) {
    if !generics.params.is_empty() {
        errors.push(syn::Error::new(
            generics.span(),
            "generics are not allowed here",
        ));
    }
}
