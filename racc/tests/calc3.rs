/*
%pure-parser

%parse-param { int regs[26] }
%parse-param { int *base }

%lex-param { int *base }

%{
# include <stdio.h>
# include <ctype.h>

#ifdef YYBISON
#define YYSTYPE int
#define YYLEX_PARAM base
#define YYLEX_DECL() yylex(YYSTYPE *yylval, int *YYLEX_PARAM)
#define YYERROR_DECL() yyerror(int regs[26], int *base, const char *s)
int YYLEX_DECL();
static void YYERROR_DECL();
#endif

%}
*/

struct Context {
    regs: Vec<i32>,
}

racc::racc_grammar! {

    type Context = Context;
    type Value = i32;




// %start list

DIGIT;
LETTER;

/*

left '|'
left '&'
left '+' '-'
left '*' '/' '%'
left UMINUS   /* supplies precedence for unary minus */
*/


// %% /* beginning of rules section */

list  : { 0 }  /* empty */
      |  list stat { 0 } // '\n'
      |  list error // '\n'
            {
                0 //yyerrok;
            }
      ;

stat  :  expr
            {
                // printf("%d\n",$1);
                0
            }
      |  LETTER '=' expr
            {
                0 // regs[$1] = $3;
            }
      ;

expr  :  '(' expr=a ')'
            {
                a
            }
      |  expr=a '+' expr=b { a + b }
      |  expr=a '-' expr=b { a - b }
      |  expr=a '*' expr=b { a * b }
      |  expr=a '/' expr=b { a / b }
      |  expr=a '%' expr=b { a % b }
      |  expr=a '&' expr=b { a & b }
      |  expr=a '|' expr=b { a | b }

                /*
      |  '-' expr %prec UMINUS
            {  // $$ = - $2;
            }
            */

      |  LETTER=i { context.regs[i as usize] }
      |  number { 0 }
      ;

number:  DIGIT { 0  // $$ = $1; (*base) = ($1==0) ? 8 : 10;
        }
      | number DIGIT
         { 0 // $$ = (*base) * $1 + $2;
        }
      ;

// %% /* start of programs */
}
/*

#ifdef YYBYACC
extern int YYLEX_DECL();
#endif

int
main (void)
{
    int regs[26];
    int base = 10;

    while(!feof(stdin)) {
    yyparse(regs, &base);
    }
    return 0;
}

#define UNUSED(x) ((void)(x))

static void
YYERROR_DECL()
{
    UNUSED(regs); /* %parse-param regs is not actually used here */
    UNUSED(base); /* %parse-param base is not actually used here */
    fprintf(stderr, "%s\n", s);
}

int
YYLEX_DECL()
{
    /* lexical analysis routine */
    /* returns LETTER for a lower case letter, yylval = 0 through 25 */
    /* return DIGIT for a digit, yylval = 0 through 9 */
    /* all other characters are returned immediately */

    int c;

    while( (c=getchar()) == ' ' )   { /* skip blanks */ }

    /* c is now nonblank */

    if( islower( c )) {
    *yylval = (c - 'a');
    return ( LETTER );
    }
    if( isdigit( c )) {
    *yylval = (c - '0') % (*base);
    return ( DIGIT );
    }
    return( c );
}
*/
