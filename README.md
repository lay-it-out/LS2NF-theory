# Ambiguity Theory in Coq for Lay-It-Out

## Prerequisites

- Makefile
- OCaml Package Manager `opam` (>= 2.0, we tested under 2.1.1)

On Mac OS, you may install `opam` via `brew install opam` if you use Homebrew.

## Build

First add iris-dev repository and create a local opam switch:
```sh
opam repository add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git --set-default      # resolve coq-stdpp dev versions
opam switch create . ocaml-base-compiler.4.12.0
```
Enter `y` when opam asks you to install the dependencies. This step can take a while.

Next, compile this project by:
```sh
make builddep
make
```

## Correspondence to Paper Theorems

| Theorem       | Coq file                  | Name                          |
| :------------ | :------------------------ | :---------------------------- |
| Lemma 4.3     | `theories/sub_derive.v`   | `reachable_spec`              |
| Theorem 4.6   | `theories/ambiguity.v`    | `derive_amb_iff_local_amb`    |
| Lemma 5.1     | `theories/encoding.v`     | `Φ_derive_spec`               |
| Lemma 5.2     | `theories/encoding.v`     | `Φ_reach_empty_spec`          | 
| Lemma 5.3     | `theories/encoding.v`     | `Φ_reach_nonempty_spec`       |
| Lemma 5.4     | `theories/encoding.v`     | `Φ_multi_usable_spec`         |
| Theorem 5.5   | `theories/encoding.v`     | `Φ_amb_sound`                 |
| Theorem 5.6   | `theories/encoding.v`     | `Φ_amb_complete`              |
