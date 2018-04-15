.PHONY: pack all run clean
GENERATED=src/parser.mli src/parser.ml src/lexer.ml
OCAMLC=ocamlc str.cma # ocamlopt for speed
PACKAGE=hw2.zip

ifeq ($(OS),Windows_NT)
	DEL=del /f
else
	DEL=rm -f
endif

all: main.exe

run: main.exe
	./main.exe

src/tree.cmi:
	cd src && $(OCAMLC) -c tree.ml

src/annotator.cmi: $(GENERATED) src/tree.cmi
	cd src && $(OCAMLC) -c tree.ml

main.exe: src/annotator.cmi
	cd src && $(OCAMLC) tree.ml $(GENERATED:src/%=%) annotator.ml main.ml -o ../main.exe

pack: $(GENERATED)
	zip $(PACKAGE) -r Makefile src

$(GENERATED): src/lexer.mll src/parser.mly
	ocamllex src/lexer.mll 
	ocamlyacc src/parser.mly

clean:
	cd src && $(DEL) $(GENERATED:src/%=%) *.c* *.o*
	$(DEL) main.exe $(PACKAGE)
