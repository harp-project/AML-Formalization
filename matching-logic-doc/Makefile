PATH_TO_COMPILED_LIBRARY ?= ../matching-logic
DOCDIR ?= /usr/share

default: coqdoc alectryon

coqdoc: doc/coqdoc

doc/coqdoc:
	mkdir -p doc/coqdoc
	find $(PATH_TO_COMPILED_LIBRARY) -name \*.v \
		| xargs coqdoc --utf8 --parse-comments --no-index --lib-name "File" -toc -html -gallina --external https://plv.mpi-sws.org/coqdoc/stdpp/ stdpp \
		-d doc/coqdoc


install-coqdoc: doc/coqdoc
	install -d $(DOCDIR)/$(INSTALLCOQDOCROOT)/doc/coqdoc/
	$(HIDE)for i in doc/coqdoc/*; do \
	 dest="$(DOCDIR)/$(INSTALLCOQDOCROOT)/$$i";\
	 install -m 0644 "$$i" "$$dest";\
	 echo INSTALL "$$i" "$$dest";\
	done

alectryon: doc/alectryon

doc/alectryon:
	coqc --version
	sertop --version
	mkdir -p doc/alectryon
	find $(PATH_TO_COMPILED_LIBRARY) -name \*.v \
		| parallel -j+0 --joblog paralel.log --halt-on-error 2 --ungroup -v -- ./run_alectryon.sh "$(PATH_TO_COMPILED_LIBRARY)"

install-alectryon: doc/alectryon
	install -d $(DOCDIR)/$(INSTALLCOQDOCROOT)/doc/alectryon/
	$(HIDE)for i in doc/alectryon/*; do \
	 dest="$(DOCDIR)/$(INSTALLCOQDOCROOT)/$$i";\
	 install -m 0644 "$$i" "$$dest";\
	 echo INSTALL "$$i" "$$dest";\
	done
