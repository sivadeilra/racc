%pure-parser

%parse-param { int regs[26] }
%parse-param { int *base }

%lex-param { int *base }

%{

%}

%start Expr

%token PLUS MINUS LPAREN RPAREN NUM IF ELSE COMMA THEN WHILE DO DIVIDE

%% /* beginning of rules section */

Expr : NUM
    | Expr PLUS Expr
    | Expr MINUS Expr
    | Expr DIVIDE Expr
    | LPAREN Expr RPAREN
    | IF Expr THEN Expr
    | IF Expr THEN Expr ELSE Expr
    ;


%% /* start of programs */
