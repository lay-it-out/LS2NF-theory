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

# Create a virtual Opam package with the same deps, but no
# build. Uses a very ugly hack to use sed for removing the last 4
# lines since head -n -4 does not work on MacOS
# (https://stackoverflow.com/a/24298204)
builddep/ambig-builddep.opam: ambig.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@sed '$$d' $< | sed '$$d' | sed '$$d' | sed '$$d' | sed -E 's/^name: *"(.*)" */name: "\1-builddep"/' > $@

# Install the virtual Opam package to ensure that:
#  1) dependencies are installed,
#  2) they will remain satisfied even if other packages are updated/installed,
#  3) we do not have to pin the RefinedC package itself (which takes time).
builddep: builddep/ambig-builddep.opam
	@echo "# Installing package $^."
	@opam install $(OPAMFLAGS) $^
.PHONY: builddep
