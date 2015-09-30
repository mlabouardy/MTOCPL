open type_grammar;;

let main = 
  print_string (term_to_type (Parser.parse_term 
				  "if (iszero false) then 1 else false"
			       ));
  print_newline();;
