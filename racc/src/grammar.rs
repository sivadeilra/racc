/* keyword codes */

use crate::Item;
use crate::Rule;
use crate::SymbolOrRule;
use crate::Var;
use crate::{Symbol, Token};

pub const TOKEN: u8 = 0;

// the undefined value
pub const UNDEFINED: i16 = -1;

// Defines a grammar.  A grammar has these elements:
//
//     * a set of tokens (terminals), each having a name and potentially a value
//     * a set of variables (non-terminals)
//     * a set of rules, in the form A <- B C ... , where A is a variable and B and C are
//       any combination of tokens or variables
//     * (optional) precedence and associativity rules for rules
//
pub struct Grammar {
    // the symbols (non-terminals and terminals/tokens)
    // symbols are ordered as tokens first, then non-terminals.
    // symbol[0] is the special $end token.
    // the first non-terminal is the special "$accept" symbol.
    pub nsyms: usize,
    pub ntokens: usize,
    pub nvars: usize,
    // pub start_symbol: usize,
    /// len = nsyms
    pub name: Vec<syn::Ident>,

    pub pname: Vec<String>,

    /// len = nsyms
    pub value: Vec<i16>,

    // these two are managed differently
    pub prec: Vec<i16>,
    pub assoc: Vec<u8>,

    // the rules which describe the grammar
    pub nrules: usize,

    // len = nitems
    pub ritem: Vec<SymbolOrRule>,

    /// Rule -> Symbol
    /// Gives the LHS symbol of each rule
    pub rlhs: Vec<Symbol>,

    /// Rule -> Item
    /// Contains the item (index in ritem) of the first symbol on the RHS.
    pub rrhs: Vec<Item>,

    /// Rule -> precedence
    pub rprec: Vec<i16>,

    /// Rule -> associativity
    pub rassoc: Vec<u8>,
}

impl Grammar {
    pub fn is_var(&self, s: Symbol) -> bool {
        (s.0 as usize) >= self.ntokens
    }

    pub fn is_token(&self, s: Symbol) -> bool {
        (s.0 as usize) < self.ntokens
    }

    pub fn start(&self) -> Symbol {
        Symbol(self.ntokens as i16)
    }

    pub fn nitems(&self) -> usize {
        self.ritem.len()
    }

    pub fn ritem(&self, item: Item) -> SymbolOrRule {
        self.ritem[item.0 as usize]
    }

    pub fn name(&self, symbol: Symbol) -> &syn::Ident {
        &self.name[symbol.0 as usize]
    }

    pub fn rule_to_str(&self, r: Rule) -> String {
        let mut s = String::new();
        s.push_str(&format!("(r{}) {} :", r, self.name(self.rlhs(r))));
        for &sym in self.rule_rhs_syms(r).iter() {
            let sym = sym.as_symbol();
            s.push_str(&format!(" {}", self.name(sym)));
        }
        s
    }

    pub fn rule_rhs_syms(&self, rule: Rule) -> &[SymbolOrRule] {
        let start = self.rrhs[rule.0 as usize].0 as usize;
        let end = self.rrhs[rule.0 as usize + 1].0 as usize - 1;
        &self.ritem[start..end]
    }

    pub fn get_rhs_items(&self, r: Rule) -> &[SymbolOrRule] {
        let rhs = self.rrhs[r.0 as usize];
        assert!(rhs.0 >= 0);
        let mut end = rhs.0 as usize;
        while self.ritem[end].is_symbol() {
            end += 1;
        }
        &self.ritem[rhs.0 as usize..end]
    }

    pub fn symbol_to_var(&self, sym: Symbol) -> Var {
        let su = sym.0 as usize;
        assert!(su >= self.ntokens);
        Var((su - self.ntokens) as i16)
    }

    pub fn symbol_to_token(&self, sym: Symbol) -> Token {
        assert!((sym.0 as usize) < self.ntokens);
        Token(sym.0)
    }

    pub fn var_to_symbol(&self, var: Var) -> Symbol {
        assert!((var.0 as usize) < self.nvars);
        Symbol(self.ntokens as i16 + var.0)
    }

    #[allow(dead_code)]
    pub fn symbol_to_var_opt(&self, sym: Symbol) -> Option<Var> {
        let su = sym.0 as usize;
        if su >= self.ntokens {
            Some(Var((su - self.ntokens) as i16))
        } else {
            None
        }
    }

    pub fn iter_vars(&self) -> impl Iterator<Item = Var> {
        (0..self.nvars).map(move |i| Var(i as i16))
    }

    pub fn iter_var_syms(&self) -> impl Iterator<Item = Symbol> {
        (self.ntokens..self.nsyms).map(move |i| Symbol(i as i16))
    }

    pub fn iter_token_syms(&self) -> impl Iterator<Item = Symbol> {
        (0..self.ntokens).map(move |i| Symbol(i as i16))
    }

    pub fn iter_rules(&self) -> impl Iterator<Item = Rule> {
        (0..self.nrules).map(move |i| Rule(i as i16))
    }

    pub fn rlhs(&self, rule: Rule) -> Symbol {
        self.rlhs[rule.0 as usize]
    }

    pub fn rrhs(&self, rule: Rule) -> Item {
        self.rrhs[rule.0 as usize]
    }
}
