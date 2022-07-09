all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all matching_logic.glob

# This target is parameterized by the variable $(MATCHINGLOGICGLOB)
# which should point to 'matching_logic.glob' of the built (and possibly installed)
# library.
html: Makefile.coq
	@+$(MAKE) -f Makefile.coq html_nodep \
	 COQDOCEXTRAFLAGS="--gallina --external https://plv.mpi-sws.org/coqdoc/stdpp/ stdpp"

install: Makefile.coq
	@+$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf ${MATCHINGLOGICGLOB}

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force install
