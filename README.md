# Layout Sensitive Binary Normal Form (LS2NF) Theories

[![Build][build-badge]][build-link]

[build-badge]: https://github.com/lay-it-out/LS2NF-theory/actions/workflows/build.yml/badge.svg?branch=main
[build-link]: https://github.com/lay-it-out/LS2NF-theory/actions/workflows/build.yml

This repository contains the Coq formulation on LS2NF proposed in the Lay-it-out paper.

## Build

### Via Nix

Install dependencies and compile Coq code via the following command:

```sh
nix develop
```

In the nix developing environment shell, manually step into the proof using your favorite Coq IDE, such as VS Code:

```sh
(nix:coq8.17-LS2NF-dev-env) $ code .
```

### Via Docker

```sh
docker build .
```

This automatically creates an image with all dependencies installed and all Coq files checked.


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
