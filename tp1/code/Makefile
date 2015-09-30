OCAMLC = ocamlc -g

all: main lib

base:
	ocamllex type_lexer.mll && \
	ocamlyacc type_parser.mly && \
	$(OCAMLC) -c syntax.ml type_parser.mli

lib: base
	$(OCAMLC) syntax.ml type_parser.ml type_lexer.ml parser.ml \
	-a -o syntax.cma

main: base
	$(OCAMLC) -w x -o syntax \
	syntax.ml type_parser.ml type_lexer.ml parser.ml main.ml

latex: main
	./syntax > result.tex && pdflatex syntax.tex

clean:
	rm -f *~ *.cm* syntax *.o *.aux *.log *.mli \
		type_lexer.ml type_parser.ml result.tex
