# Ambiguity Theory in Coq for Lay-It-Out

## Prerequisites

- Makefile
- OCaml Package Manager `opam` (>= 2.0, we tested under 2.1.1)

On Mac OS, you may install `opam` via `brew install opam` if you use Homebrew.

## Build

First add iris-dev repository and create a local opam switch:
```sh
opam repository add iris-dev --set-default      # resolve coq-stdpp dev versions
opam switch create . ocaml-base-compiler.4.12.0
```
Enter `y` when opam asks you to install the dependencies. This step can take a while.

Next, compile this project by:
```sh
make builddep
make
```
