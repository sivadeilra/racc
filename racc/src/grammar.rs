use crate::Item;
use crate::Rule;
use crate::SymbolOrRule;
use crate::Var;
use crate::{Symbol, Token};
use syn::Ident;

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
pub(crate) struct Grammar {
    // the symbols (non-terminals and terminals/tokens)
    // symbols are ordered as tokens first, then non-terminals.
    // symbol[0] is the special $end token.
    // the first non-terminal is the special "$accept" symbol.
    pub nsyms: usize,
    pub ntokens: usize,
    pub nvars: usize,

    /// len = nsyms
    pub name: Vec<Ident>,

    /// len = nsyms
    pub value: Vec<i16>,

    /// len = nsyms
    pub sym_type: Vec<Option<syn::Type>>,

    // these two are managed differently
    pub prec: Vec<i16>,
    pub assoc: Vec<Assoc>,

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
    pub rassoc: Vec<Assoc>,

    /// The ideal spans to use when reporting errors for a rule.  (len = nrules)
    pub rule_span: Vec<proc_macro2::Span>,

    /// The actions (code blocks) provided by the grammar author, if any.
    /// index = rule index
    /// len = nrules
    pub rule_blocks: Vec<Option<syn::Block>>,

    /// identifier used by grammar for a RHS value, given by =foo
    /// indices are same as rrhs
    pub rhs_binding: Vec<Option<Box<RhsBinding>>>,

    pub context_ty: Option<syn::Type>,

    /// If `enum Token` was defined with generics, e.g. `enum Token<'a>`, then this contains
    /// the generic parameters.
    pub token_generics: syn::Generics,

    pub token_attrs: Vec<syn::Attribute>,
}

#[derive(Clone)]
pub struct RhsBinding {
    pub ident: syn::Ident,
    pub ty: Option<syn::Type>,
}

impl Grammar {
    pub fn is_var(&self, s: Symbol) -> bool {
        s.index() >= self.ntokens
    }

    pub fn is_token(&self, s: Symbol) -> bool {
        s.index() < self.ntokens
    }

    pub fn start(&self) -> Symbol {
        Symbol(self.ntokens as i16)
    }

    /// The "goal" variable, as defined by the grammar. This is distinct from the `start` symbol.
    pub fn goal(&self) -> Symbol {
        Symbol(self.ntokens as i16 + 1)
    }

    pub fn nitems(&self) -> usize {
        self.ritem.len()
    }

    pub fn ritem(&self, item: Item) -> SymbolOrRule {
        self.ritem[item.index()]
    }

    pub fn name(&self, symbol: Symbol) -> &Ident {
        &self.name[symbol.index()]
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
        let start = self.rrhs[rule.index()].index();
        let end = self.rrhs[rule.index() + 1].index() - 1;
        &self.ritem[start..end]
    }

    pub fn get_rhs_items(&self, r: Rule) -> &[SymbolOrRule] {
        let rhs = self.rrhs[r.index()];
        assert!(rhs.0 >= 0);
        let mut end = rhs.index();
        while self.ritem[end].is_symbol() {
            end += 1;
        }
        &self.ritem[rhs.index()..end]
    }

    pub fn symbol_to_var(&self, sym: Symbol) -> Var {
        let su = sym.index();
        assert!(su >= self.ntokens);
        Var((su - self.ntokens) as i16)
    }

    pub fn symbol_to_token(&self, sym: Symbol) -> Token {
        assert!(sym.index() < self.ntokens);
        Token(sym.0)
    }

    pub fn var_to_symbol(&self, var: Var) -> Symbol {
        assert!(var.index() < self.nvars);
        Symbol(self.ntokens as i16 + var.0)
    }

    pub fn iter_vars(&self) -> impl Iterator<Item = Var> {
        (0..self.nvars).map(move |i| Var(i as i16))
    }

    pub fn iter_var_syms(&self) -> impl Iterator<Item = Symbol> {
        (self.ntokens..self.nsyms).map(move |i| Symbol(i as i16))
    }

    #[allow(dead_code)] // work in progress
    pub fn iter_token_syms(&self) -> impl Iterator<Item = Symbol> {
        (0..self.ntokens).map(move |i| Symbol(i as i16))
    }

    pub fn iter_rules(&self) -> impl Iterator<Item = Rule> {
        (0..self.nrules).map(move |i| Rule(i as i16))
    }

    pub fn rlhs(&self, rule: Rule) -> Symbol {
        self.rlhs[rule.index()]
    }

    pub fn rrhs(&self, rule: Rule) -> Item {
        self.rrhs[rule.index()]
    }

    /// Gets the best `Span` for this rule. Ideally, this is the definition of the rule.
    pub fn rule_span(&self, rule: Rule) -> proc_macro2::Span {
        self.rule_span[rule.index()]
    }
}

#[repr(u8)]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
#[allow(clippy::upper_case_acronyms)]
pub(crate) enum Assoc {
    TOKEN = 0,
    LEFT = 1,
    RIGHT = 2,
    // NONASSOC = 3,
}

// pub const TOKEN: u8 = 0;
// pub(crate) const LEFT: u8 = 1;
// pub(crate) const RIGHT: u8 = 2;
