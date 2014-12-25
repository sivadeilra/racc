use std::fmt::Show;

#[deriving(Copy,Show)]
pub enum PushTokenResult {
    Ok,                         // The token was consumed.
    SyntaxError
}

pub enum ParseEndResult<SymbolValue> {
    Accepted(SymbolValue),
    SyntaxError
}

#[deriving(Copy)]
pub struct ParserTables<SymbolValue:Show, AppContext> {
    pub yyrindex: &'static [u16],
    pub yysindex: &'static [u16],
    pub yygindex: &'static [u16],
    pub yytable: &'static [u16],
    pub yydgoto: &'static [u16],
    pub yydefred: &'static [u16],
    pub yylhs: &'static [u16],
    pub yylen: &'static [u16],
    pub yycheck: &'static [u16],
    pub yyname: &'static [&'static str],
    pub yyfinal: uint,

    // for debugging
    pub yyrules: &'static [&'static str],

    pub reduce: fn(parser: &mut Vec<SymbolValue>, reduction: uint, ctx: &mut AppContext) -> SymbolValue
}

// #[deriving(Clone)]
pub struct ParserState<SymbolValue:Show, AppContext> {
    pub tables: ParserTables<SymbolValue, AppContext>,
    pub yystate: uint,
    pub value_stack: Vec<SymbolValue>,
    pub state_stack: Vec<uint>,
}

impl<SymbolValue:Show, AppContext> ParserState<SymbolValue, AppContext> {
    pub fn new(tables: ParserTables<SymbolValue, AppContext>) -> ParserState<SymbolValue, AppContext> {
        ParserState {
            tables: tables,
            yystate: 0,
            value_stack: Vec::new(),
            state_stack: { let mut v = Vec::with_capacity(20); v.push(0); v }
        }
    }

    fn yyreduce(&mut self, reduction: uint, ctx: &mut AppContext) {
        let len = self.tables.yylen[reduction] as uint;
        let lhs = self.tables.yylhs[reduction];

        debug!("state {} reducing by rule {}, len={}, lhs={}", self.yystate, self.tables.yyrules[reduction], len, lhs);
        assert!(self.value_stack.len() >= len);
        assert!(self.state_stack.len() >= len);

        // Invoke the generated "reduce" method.  This method handles popping values from
        // parser.values_stack, and then executing the app-supplied code for this reduction.
        // Because the generated code handles popping items from the stack, it is not necessary
        // for us to consult a 'yylen' table here; that information is implicit.
        let old_values_len = self.value_stack.len();
        let reduce_value = (self.tables.reduce)(&mut self.value_stack, reduction, ctx);
        assert!(self.value_stack.len() + len == old_values_len);
        debug!("    generated code popped {} values from value stack, new len = {}", old_values_len, self.value_stack.len());
        // Push the value that represents the reduction of this rule (the LHS).
        debug!("    after pushing the result of the reduction, value_stack.len = {}, reduce_value={}", self.value_stack.len() + 1, reduce_value);
        self.value_stack.push(reduce_value);

        // pop states
        for _ in range(0, len) {
            self.state_stack.pop().unwrap();
        }
        let top_state = self.state_stack[self.state_stack.len() - 1] as uint;

        self.yystate = top_state;

        if top_state == 0 && lhs == 0 {
            debug!("        after reduction, shifting from state 0 to state {} (0/0 case!)", self.tables.yyfinal);
            self.yystate = self.tables.yyfinal;
            self.state_stack.push(self.tables.yyfinal);

            // todo: port acceptance code
        }
        else {
            let yyn_0 = self.tables.yygindex[lhs as uint] as i16;
            let yyn_1 = yyn_0 + (self.yystate as i16);

            // debug!("        checking gindex, yym={}, yyn_0={}, yyn_1={}, YYCHECK[yyn_1]={}", lhs, yyn_0, yyn_1, self.tables.yycheck[yyn_1 as uint]);
            let next_state: uint = if (self.tables.yycheck[yyn_1 as uint] as uint) == self.yystate {
                // debug!("        yystate = yytable[{}] = {}", yyn_1, self.tables.yytable[yyn_1 as uint]);
                self.tables.yytable[yyn_1 as uint] as uint
            }
            else {
                // debug!("         yystate = yydgoto[{}] = {}", reduction, self.tables.yydgoto[lhs as uint]);
                self.tables.yydgoto[lhs as uint] as uint
            };
            debug!("        after reduction, shifting from state {} to state {}", self.yystate, next_state);

            self.yystate = next_state;
            self.state_stack.push(next_state);
        }
    }

    fn do_defreds(&mut self, ctx: &mut AppContext) {
        // Check for default reductions.
        loop {
            let defred = self.tables.yydefred[self.yystate];
            if defred != 0 {
                // debug!("    default reduction: yyn={}", defred);
                self.yyreduce(defred as uint, ctx);
            }
            else {
                // debug!("    no more defreds");
                break;
            }
        }
    }

    fn try_shift(&mut self, token: u32, lval: SymbolValue) -> bool {
        // Check to see if there is a SHIFT action for this (state, token).
        let shift = self.tables.yysindex[self.yystate] as i16;
        if shift != 0 {
            let yyn = shift + (token as i16);
            assert!(yyn >= 0);
            assert!(self.tables.yycheck[yyn as uint] as i16 == token as i16);
            let next_state = self.tables.yytable[yyn as uint] as i16;
            debug!("state {}, shifting to state {}, pushing lval {}", self.yystate, next_state, lval);
            assert!(next_state >= 0);
            self.yystate = next_state as uint;
            self.state_stack.push(self.yystate);
            self.value_stack.push(lval); // <-- lval is consumed
            true
        }
        else {
            false
        }
    }

    // Check to see if there is a REDUCE action for this (state, token).
    fn try_reduce(&mut self, ctx: &mut AppContext, token: u32) -> bool {
        let red = self.tables.yyrindex[self.yystate] as i16;
        if red != 0 {
            let yyn = red + (token as i16);
            debug!("    yyn={}", yyn);
            assert!(self.tables.yycheck[yyn as uint] as i16 == token as i16);
            debug!("    reducing by {}", red);
            let rr = self.tables.yytable[yyn as uint] as uint;
            self.yyreduce(rr, ctx);
            true
        }
        else {
            false
        }
    }

    pub fn push_token(&mut self, ctx: &mut AppContext, token: u32, lval: SymbolValue) -> PushTokenResult {
        assert!(self.state_stack.len() > 0);
        // assert!(self.state_stack[parser.state_stack.len() - 1] as uint == yystate);

        // let mut yystate = self.state_stack[self.state_stack.len() - 1] as uint;

        debug!("");
        debug!("state {}, reading {} ({}) lval {}, state_stack = {}", self.yystate, token, self.tables.yyname[token as uint], lval, self.state_stack);
        debug!("value_stack = {}", self.value_stack);

        if self.try_shift(token, lval) {
            self.do_defreds(ctx);
            return PushTokenResult::Ok;
        }

        if self.try_reduce(ctx, token) {
            self.do_defreds(ctx);
            return PushTokenResult::Ok;
        }

        // If there is neither a shift nor a reduce action defined for this (state, token),
        // then we have encountered a syntax error.

        debug!("syntax error!  token is not recognized in this state.");
        return PushTokenResult::SyntaxError;
    }

    pub fn push_end(&mut self, ctx: &mut AppContext) -> ParseEndResult<SymbolValue> {
        assert!(self.state_stack.len() > 0);

        // let mut yystate = self.state_stack[self.state_stack.len() - 1] as uint;

        debug!("");
        debug!("push_end: yystate={}  state_stack = {}", self.yystate, self.state_stack);

        self.try_reduce(ctx, 0);
        self.do_defreds(ctx);

        if self.value_stack.len() == 1 {
            debug!("accept");
            let final_lval = self.value_stack.pop().unwrap();
            return ParseEndResult::Accepted(final_lval);
        }

        debug!("done with all reductions.  yystate={}  state_stack={}", self.yystate, self.state_stack);

        // If there is neither a shift nor a reduce action defined for this (state, token),
        // then we have encountered a syntax error.

        debug!("syntax error!  token is not recognized in this state.");
        return ParseEndResult::SyntaxError;
    }
}
