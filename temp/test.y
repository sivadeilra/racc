%{

#include <stdlib.h>

#define YYDEBUG 1

%}

/*%start Expr*/

%token PLUS
%token MINUS
%token LPAREN
%token RPAREN
%token NUM
%token IF
%token ELSE
%token COMMA
%token THEN
%token WHILE
%token DO

%%

	Expr : NUM
		| Expr PLUS Expr { printf("reduce by addition: %d + %d\n", $1, $3); $$ = $1 + $3; }
		| Expr MINUS Expr { printf("reduce by subtraction: %d - %d\n", $1, $3); $$ = $1 - $3; }
		| ParenExpr
		| IfExpr
		| WhileExpr;

	ParenExpr : LPAREN Expr RPAREN { printf("grouping\n"); };

	IfExpr : IF ParenExpr THEN Expr
		| IF ParenExpr THEN Expr ELSE Expr;

	WhileExpr : WHILE ParenExpr DO Expr;

%%

int yylval_next = 100;

int g_tokens[] = {
    LPAREN,
    NUM,
    RPAREN,
    PLUS,
    NUM,
    -1
};

int g_token_index = 0;

int yylex() {
    int tok = g_tokens[g_token_index];
    yylval = yylval_next;

    if (tok != -1) {
        g_token_index++;
        yylval_next++;
    }

    return tok;
}

int main() {

    yyparse();

    return 0;

}

void yyerror(const char *s)
{
    printf("yyerror: %s\n", s);
    exit(1);
}
