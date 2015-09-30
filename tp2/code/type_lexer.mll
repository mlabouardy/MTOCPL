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
  | "all"           { FORALL }
  | '.'             { DOT }
  | ','             { COMMA }
  | ':'             { COLON }
  | '='             { EQUAL }
  | "=="            { BEQUAL }
  | "->"            { ARROW  }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | '['             { LBRACKET }
  | ']'             { RBRACKET }
  | ['a'-'z']+ as s { VAR(s) }
  | eof             { EOF }
