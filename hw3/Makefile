.PHONY: pack all run clean
GENERATED=src/parser.mli src/parser.ml src/lexer.ml
OCAMLC=ocamlc str.cma #ocamlopt str.cmxa
PACKAGE=hw3.zip

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

src/utils.cmi: src/tree.cmi $(GENERATED)
	cd src && $(OCAMLC) -c tree.ml $(GENERATED:src/%=%) utils.ml

src/annotator.cmi: src/utils.cmi src/tree.cmi $(GENERATED)
	cd src && $(OCAMLC) -c $(GENERATED:src/%=%) annotator.ml
	
src/deduction.cmi: src/annotator.cmi
	cd src && $(OCAMLC) -c deduction.ml
	
src/main.cmi: src/deduction.cmi
	cd src && $(OCAMLC) -c main.ml

main.exe: src/main.cmi
	cd src && $(OCAMLC) tree.ml $(GENERATED:src/%=%) utils.ml annotator.ml deduction.ml main.ml -o ../main.exe

pack: $(GENERATED)
	zip $(PACKAGE) -r Makefile src proofs

$(GENERATED): src/lexer.mll src/parser.mly
	ocamllex src/lexer.mll 
	ocamlyacc src/parser.mly

clean:
	cd src && $(DEL) $(GENERATED:src/%=%) *.c* *.o*
	$(DEL) main.exe $(PACKAGE)
