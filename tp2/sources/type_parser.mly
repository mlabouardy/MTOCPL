%{ 
  open Type_grammar
%}

%token <int> INT
%token <string> VAR
%token TRUE FALSE SUCC BEQUAL EQUAL 
%token LPAREN RPAREN LBRACKET RBRACKET COLON COMMA DOT
%token LAMBDA LET IN IF THEN ELSE ARROW FORALL
%token EOF

%start expr
%type <Type_grammar.term> expr
%start typ
%type <Type_grammar.ty> typ
%%

var:
| VAR { $1 }
;

var_list:
| var COMMA var_list { $1 :: $3 }
| var                { [$1] }
;

typ:
| var               { match $1 with  
		      | "nat"  -> TyNat
		      | "bool" -> TyBool
		      | _      -> TyId $1 }
| typ ARROW typ     { (TyArr ($1, $3)) }
| LPAREN typ RPAREN { $2 }
;

expr:
| var                             { TmVar ($1,Unk) }
| INT                             { int_to_term $1 }
| TRUE                            { TmTrue }
| FALSE                           { TmFalse }
| LPAREN expr RPAREN              { $2 }
| SUCC expr                       { TmSucc $2 }
| LAMBDA LPAREN var COLON typ RPAREN ARROW expr { TmAbs ($3,$5,$8) }
| LAMBDA var ARROW expr           { TmAbs ($2,Unk,$4) }
| expr expr                       { TmApp ($1,$2) }
| IF expr THEN expr ELSE expr     { TmIf  ($2,$4,$6,Unk) }
;

