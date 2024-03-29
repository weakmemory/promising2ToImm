COQMODULE    := promising2ToImm 
COQTHEORIES  := src/lib/*.v src/ext_traversal/*.v src/promise_basics/*.v src/simulation/*.v src/cert_graph/*.v src/interval_allocation/*.v src/reserve_steps/*.v src/simulation_steps/*.v src/compilation/*.v

.PHONY: all theories clean tounicode

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

vio: Makefile.coq
	$(MAKE) -f Makefile.coq vio 

checkproofs: Makefile.coq
	$(MAKE) -f Makefile.coq checkproofs

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
