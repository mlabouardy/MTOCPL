OCAMLC = ocamlc -g
# OCAMLC = ocamlopt

all: type_inference

type_inference:
	ocamllex type_lexer.mll && \
	ocamlyacc type_parser.mly && \
	$(OCAMLC) -c type_grammar.ml type_parser.mli && \
	$(OCAMLC) -c type_grammar.ml type_parser.ml && \
	$(OCAMLC) type_grammar.ml type_parser.ml type_lexer.ml type_inference.ml -o type_inference

clean:
	rm -f *~ *.cm* type_inference *.o
