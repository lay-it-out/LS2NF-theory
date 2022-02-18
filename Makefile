all:
	@dune build _build/default/ambig.install --display short
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

builddep-opamfiles: builddep/ambig-builddep.opam
	@true
.PHONY: builddep-opamfiles

builddep/ambig-builddep.opam: ambig.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@sed '$$d' $< | sed '$$d' | sed '$$d' | sed '$$d' | sed -E 's/^name: *"(.*)" */name: "\1-builddep"/' > $@

builddep: builddep/ambig-builddep.opam
	@echo "# Installing package $^."
	@opam install $(OPAMFLAGS) $^
.PHONY: builddep
