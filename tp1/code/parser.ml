open Syntax;;

(*************************************************************)
(*                    Parse helpers                          *)
(*************************************************************)
let handle_parse_error lexbuf str exn =
  let curr = lexbuf.Lexing.lex_curr_p in
  let line = curr.Lexing.pos_lnum in
  let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  Printf.fprintf stderr "!! Syntax error line %d, col %d\n" line cnum;
  Printf.fprintf stderr "%s\n" str;
  Printf.fprintf stderr "%s^^^\n" (String.make (max (cnum-2) 0) ' ');
  raise exn;;

let parse_term str =
  let lexbuf = Lexing.from_string str in
  try  Type_parser.expr Type_lexer.lex lexbuf
  with exn -> handle_parse_error lexbuf str exn;;

