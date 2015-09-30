(*************************************************************)
(*                Simple grammar for terms                   *)
(*************************************************************)
type id = string    (* Identifiers *)

type term =
  | TmTrue | TmFalse              (* Booleans    *)
  | TmZero | TmSucc of term       (* Naturals    *)
  | TmIsZ  of term                (* Zero test   *)
  | TmIf   of term * term * term  (* Conditional *)

(* String helpers *)
let bold_string s = "\\textbf{"^s^"}";;
let blue_string s = "\\textcolor{blue!90!black}{"^s^"}";;
let red_string s  = "\\textcolor{red!80!black}{"^s^"}";;
let vio_string s  = "\\textcolor{red!40!blue}{"^s^"}";;

(* Function that transforms a term into a string *)
let rec term_to_string t = 
  match t with
  | TmTrue       -> blue_string "T"
  | TmFalse      -> blue_string "F"
  | TmZero       -> red_string "0"
  | TmSucc u     -> "S"^(term_to_string u)
  | TmIsZ u      -> "iszero "^(term_to_string u)
  | TmIf (i,u,e) -> (bold_string "if")^" "
		    ^(term_to_string i)^" "^(bold_string "then")^" "
		    ^(term_to_string u)^" "^(bold_string "else")^" "
		    ^(term_to_string e)

let rec int_to_term n = if (n == 0) then TmZero
                        else TmSucc (int_to_term (n-1));;
		
