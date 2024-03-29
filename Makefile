all:
	@dune build _build/default/LS2NF.install --display short
.PHONY: all

install:
	@dune install
.PHONY: install

uninstall:
	@dune uninstall
.PHONY: uninstall

doc:
	LS2NF_ROOT=`pwd` dune build theories/LS2NF.html/
	rm -rf doc/
	cp -R _build/default/theories/LS2NF.html/ doc/
	cp -R coqdocjs/resources/ doc/
.PHONY: doc

clean:
	@dune clean
	rm -rf doc/
.PHONY: clean