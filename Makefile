COQMODULE    := promise2ToImm 
COQTHEORIES  := src/lib/*.v src/traversal/*.v src/ext_traversal/*.v src/promise_basics/*.v src/simulation/*.v src/simulation_steps/*.v

.PHONY: all theories clean tounicode

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

quick-check: Makefile.coq
	$(MAKE) -f Makefile.coq vio2vo J=8

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src $(COQMODULE)"; \
	echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq

tounicode:
	sed -i 's/<</⟪/g' $(COQTHEORIES) 
	sed -i 's/>>/⟫/g' $(COQTHEORIES)
	sed -i 's/;;/⨾/g' $(COQTHEORIES)
	sed -i 's/<|/⦗/g' $(COQTHEORIES)
	sed -i 's/|>/⦘/g' $(COQTHEORIES)
	sed -i 's/\^+/⁺/g' $(COQTHEORIES)
	sed -i 's/\^\*/＊/g' $(COQTHEORIES)
