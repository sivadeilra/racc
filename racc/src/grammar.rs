/* keyword codes */

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
    pub ritem: Vec<i16>,

    pub rlhs: Vec<i16>,
    pub rrhs: Vec<i16>,
    pub rprec: Vec<i16>,
    pub rassoc: Vec<u8>,
}

impl Grammar {
    pub fn is_var(&self, s: i16) -> bool {
        (s as usize) >= self.start_symbol
    }

    pub fn is_token(&self, s: i16) -> bool {
        (s as usize) < self.start_symbol
    }

    pub fn nitems(&self) -> usize {
        self.ritem.len()
    }

    pub fn rule_to_str(&self, r: Rule) -> String {
        let mut s = String::new();
        s.push_str(&format!("(r{}) {} :", r, self.name[self.rlhs[r as usize] as usize]));
        for it in self.ritem[self.rrhs[r as usize] as usize..].iter() {
            if *it < 0 {
                break;
            } // end of this rule
            s.push_str(&format!(" {}", self.name[*it as usize]));
        }
        s
    }

    pub fn get_rhs_items<'a>(&'a self, r: usize) -> &'a [i16] {
        let rhs = self.rrhs[r];
        assert!(rhs >= 0);
        let mut end = rhs as usize;
        while self.ritem[end] >= 0 {
            end += 1;
        }
        &self.ritem[rhs as usize..end]
    }
}
