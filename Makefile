COQMODULE    := PromisingArch
COQDIRS      := lib promising axiomatic lcertify
COQTHEORIES  := lib/hahn/*.v $(foreach dir, $(COQDIRS), src/$(dir)/*.v)

.PHONY: all theories clean

all: quick

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R lib/hahn Top"; \
   \
   echo $(foreach dir, $(COQDIRS), "-R src/$(dir) $(COQMODULE).$(dir)"); \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq Makefile.coq.conf
