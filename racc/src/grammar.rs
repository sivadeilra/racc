/* keyword codes */

use crate::SymbolOrRule;
use crate::Var;
use crate::Symbol;
use crate::Rule;

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
    pub start_symbol: usize,

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

    pub rlhs: Vec<i16>,
    pub rrhs: Vec<i16>,
    pub rprec: Vec<i16>,
    pub rassoc: Vec<u8>,
}

impl Grammar {
    pub fn is_var_old(&self, s: i16) -> bool {
        (s as usize) >= self.start_symbol
    }

    pub fn is_var(&self, s: Symbol) -> bool {
        (s.0 as usize) >= self.start_symbol
    }

    pub fn is_token(&self, s: Symbol) -> bool {
        (s.0 as usize) < self.start_symbol
    }

    pub fn nitems(&self) -> usize {
        self.ritem.len()
    }

    pub fn name(&self, symbol: Symbol) -> &syn::Ident {
        &self.name[symbol.0 as usize]
    }

    pub fn rule_to_str(&self, r: Rule) -> String {
        let mut s = String::new();
        s.push_str(&format!("(r{}) {} :", r, self.name[self.rlhs[r as usize] as usize]));
        for &it in self.ritem[self.rrhs[r as usize] as usize..].iter() {
            if it.is_rule() {
                break;
            } // end of this rule
            s.push_str(&format!(" {}", self.name(it.as_symbol())));
        }
        s
    }

    pub fn get_rhs_items<'a>(&'a self, r: usize) -> &'a [SymbolOrRule] {
        let rhs = self.rrhs[r];
        assert!(rhs >= 0);
        let mut end = rhs as usize;
        while self.ritem[end].is_symbol() {
            end += 1;
        }
        &self.ritem[rhs as usize..end]
    }

    pub fn symbol_to_var(&self, sym: Symbol) -> Var {
        let su = sym.0 as usize;
        assert!(su >= self.start_symbol);
        Var((su - self.start_symbol) as i16)
    }

    pub fn symbol_to_var_opt(&self, sym: Symbol) -> Option<Var> {
        let su = sym.0 as usize;
        if su >= self.start_symbol {
            Some(Var((su - self.start_symbol) as i16))
        } else {
            None
        }
    }
}
