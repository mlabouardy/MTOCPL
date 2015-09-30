{
open Type_parser
}

rule lex = parse
  | [' ' '\n' '\t'] { lex lexbuf }
  | ['0'-'9']+ as s { INT(int_of_string s) }
  | "succ"          { SUCC }
  | "fun"           { LAMBDA }
  | "let"           { LET }
  | "in"            { IN }
  | "if"            { IF }
  | "then"          { THEN }
  | "else"          { ELSE }
  | "true"          { TRUE }
  | "false"         { FALSE }
  | "iszero"        { ISZERO }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | ['a'-'z']+ as s { VAR(s) }
  | eof             { EOF }
