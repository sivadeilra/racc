use std::default::Default;

/* keyword codes */

pub const TOKEN: u8 =0;
/*
pub const LEFT: u8 =1;
pub const RIGHT: u8 =2;
pub const NONASSOC: u8 =3;
pub const MARK: u8 =4;
pub const TEXT: u8 =5;
pub const TYPE: u8 =6;
pub const START: u8 =7;
pub const UNION: u8 =8;
pub const IDENT: u8 =9;
pub const EXPECT: u8 =10;
pub const EXPECT_RR: u8 =11;
pub const CLASS: u8 =12;
pub const NAMESPACE: u8 =13;
pub const LANGUAGE: u8 =14;
pub const LOCATION: u8 =15;
pub const VISIBILITY: u8 =16;
*/

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
#[deriving(Default)]
pub struct Grammar
{
    // the symbols (non-terminals and terminals/tokens)
    // symbols are ordered as tokens first, then non-terminals.
    // symbol[0] is the special $end token.
    // the first non-terminal is the special "$accept" symbol.
    pub nsyms: uint,
    pub ntokens: uint,
    pub nvars: uint,
    pub start_symbol: uint,

    pub name: Vec<String>,
    pub pname: Vec<String>,
    pub value: Vec<i16>,

    // these two are managed differently
    pub prec: Vec<i16>,
    pub assoc: Vec<u8>,

    // the rules which describe the grammar
    pub nitems: uint,
    pub nrules: uint,

    pub ritem: Vec<i16>,
    pub rlhs: Vec<i16>,
    pub rrhs: Vec<i16>,
    pub rprec: Vec<i16>,
    pub rassoc: Vec<u8>,
}

impl Grammar
{
	pub fn new() -> Grammar {
        Grammar {
            nitems: 4,
            nrules: 3,
            ritem: Vec::new(),
            rlhs: Vec::new(),
            rrhs: Vec::new(),
            rprec: vec![0, 0, 0],
            rassoc: vec![TOKEN, TOKEN, TOKEN],
		    .. Default::default()
        }
	}

    pub fn is_var(&self, s: uint) -> bool
    {
        s >= self.start_symbol
    }

    pub fn is_token(&self, s: uint) -> bool
    {
        s < self.start_symbol
    }

    pub fn rule_to_str(&self, r: uint) -> String {
        let mut s = String::new();
        s.push_str(format!("(r{}) ", r).as_slice());
        s.push_str(self.name[self.rlhs[r] as uint].as_slice());
        s.push_str(" :");
        for it in self.ritem.slice_from(self.rrhs[r] as uint).iter() {
            if *it < 0 { break; } // end of this rule
            s.push_str(" ");
            s.push_str(self.name[*it as uint].as_slice());
        }
        s
    }

    pub fn get_rhs_items<'a>(&'a self, r: uint) -> &'a[i16] {
        let rhs = self.rrhs[r];
        assert!(rhs >= 0);
        let mut end = rhs as uint;
        while self.ritem[end] >= 0 {
            end += 1;
        }
        self.ritem.slice(rhs as uint, end)
    }
}
