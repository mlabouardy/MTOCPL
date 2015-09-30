type token =
  | INT of (int)
  | VAR of (string)
  | TRUE
  | FALSE
  | SUCC
  | BEQUAL
  | EQUAL
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | COLON
  | COMMA
  | DOT
  | LAMBDA
  | LET
  | IN
  | IF
  | THEN
  | ELSE
  | ARROW
  | FORALL
  | EOF

val expr :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Type_grammar.term
val typ :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Type_grammar.ty
