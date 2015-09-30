%{ 
  open Syntax
%}

%token <int> INT
%token <string> VAR
%token TRUE FALSE SUCC BEQUAL EQUAL 
%token LPAREN RPAREN LBRACKET RBRACKET 
%token LAMBDA LET IN IF THEN ELSE ISZERO
%token EOF

%start expr
%type <Syntax.term> expr
%%

var:
| VAR { $1 }
;

expr:
| INT                             { int_to_term $1 }
| TRUE                            { TmTrue }
| FALSE                           { TmFalse }
| LPAREN expr RPAREN              { $2 }
| SUCC expr                       { TmSucc $2 }
| ISZERO expr                     { TmIsZ $2 }
| IF expr THEN expr ELSE expr     { TmIf  ($2,$4,$6) }
;

