CAMLC = camlc
LEX = camllex
YACC = camlyacc

all: clean deriv

clean:
	rm -rf *.zo deriv deriv-file *.zi lexer.ml parser.ml parser.mli

deriv:
	$(CAMLC) -c types.ml
	$(LEX) lexer.mll
	$(YACC) parser.mly
	$(CAMLC) -c parser.mli
	$(CAMLC) -c lexer.ml
	$(CAMLC) -c parser.ml
	$(CAMLC) -c deriv.ml
	$(CAMLC) -c deriv-file.ml
	$(CAMLC) -o deriv lexer.zo parser.zo deriv.zo
	$(CAMLC) -o deriv-file lexer.zo parser.zo deriv-file.zo

