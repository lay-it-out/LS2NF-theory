# Layout Sensitive Binary Normal Form (LS2NF) Theories

[![Build][build-badge]][build-link]

[build-badge]: https://github.com/lay-it-out/LS2NF-theory/actions/workflows/build.yml/badge.svg?branch=main
[build-link]: https://github.com/lay-it-out/LS2NF-theory/actions/workflows/build.yml

This repository contains the Coq formulation on LS2NF proposed in the Lay-it-out paper.

## Build

### Via Docker

If you have `docker` installed, first create an image:
```sh
docker build .
```
The `Dockerfile` will be processed and all dependencies will be downloaded, compiled and installed, which may take a few minutes.

If this succeeds, the last line of std output should display the image ID:
```
 => => writing image sha256:<Image ID>
```
With this ID, you can now run the image and access its shell:
```sh
docker run -it <Image ID>
```

On that shell, compile the Coq proofs by:
```sh
coq@<Image ID>:~$ eval $(opam env)
coq@<Image ID>:~$ make
```

### Via OPAM

Alternatively, you can directly build this project on your host machine. You must first have the OCaml Package Manager `opam` (>= 2.0) installed.

First add iris-dev repository (for resolving the dev version of `stdpp`) and create a local OPAM switch:
```sh
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam switch create . ocaml-base-compiler.4.12.0
```
Enter `y` when OPAM asks you to install the dependencies.

Next, compile this project by:
```sh
make builddep   # this step can take a while
make
```

In case you see this error when typing `make`:
```
make: dune: No such file or directory
make: *** [all] Error 1
```
That means the environment is not in sync with the current OPAM switch. To fix it, execute `eval $(opam env)`.

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
