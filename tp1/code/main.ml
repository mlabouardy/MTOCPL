open Syntax;;

let main = 
  print_string (term_to_string (Parser.parse_term 
				  "if (iszero false) then true else false"
			       ));
  print_newline();;
