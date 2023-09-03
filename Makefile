all:
	@dune build _build/default/LS2NF.install --display short
	@dune build theories/LS2NF.html/
.PHONY: all

install:
	@dune install
.PHONY: install

uninstall:
	@dune uninstall
.PHONY: uninstall

clean:
	@dune clean
.PHONY: clean