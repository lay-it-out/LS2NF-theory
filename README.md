# Layout Sensitive Binary Normal Form (LS2NF) Theories

[![Build][build-badge]][build-link]

[build-badge]: https://github.com/lay-it-out/LS2NF-theory/actions/workflows/build.yml/badge.svg?branch=main
[build-link]: https://github.com/lay-it-out/LS2NF-theory/actions/workflows/build.yml


This proof relies on `stdpp`, an extended "standard library" for Coq.

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


## Paper-to-Artifact Correspondence Guide

We formulated all the definitions and theorems mentioned in sections 4 and 5. The main theorems are the soundness (Theorem 5.9) and completeness (Theorem 5.10) of our SMT encoding (section 5).

In the order in which the definitions and theorems appear in the text, the following tables list their counterparts in the Coq code. The first table shows all definitions mentioned in §3:

| Definition in paper       | Coq file               | Name of formalization                          | Notation         |
| :------------------------ | :--------------------- | :--------------------------------------------- | :--------------- |
| Positioned token          | `theories/grammar.v`   | `Record pos_token`                             | `a @ p`          |
| Sentence                  | `theories/grammar.v`   | `Definition sentence`                          |                  |
| Well-formedness           | `theories/grammar.v`   | `Definition well_formed`                       |                  |
| Layout constraints        | `theories/grammar.v`   | `Definition unary_predicate, binary_predicate` |                  |
| Definition 3.1 (LS2NF)    | `theories/grammar.v`   | `Record grammar`                               |                  |
| LS2NF clauses and rules   | `theories/grammar.v`   | `Inductive clause, production`                 | `A ↦ α`          |
| Parse trees               | `theories/grammar.v`   | `Inductive tree`                               |                  |
| Validity of parse trees   | `theories/grammar.v`   | `Inductive tree_valid`                         | `✓{G} t`         |
| Witness                   | `theories/grammar.v`   | `Definition tree_witness`                      | `t ▷ A ={G}=> w` |
| Derivation                | `theories/grammar.v`   | `Definition derive`                            | `G ⊨ A => w`     |
| Derivation ambiguity      | `theories/ambiguity.v` | `Definition derive_amb`                        |                  |

The second table shows all definitions/theorems mentioned in §4 and §5:

| Definition/Theorem in paper               | Coq file                | Name of formalization                    | Notation     |
| :---------------------------------------- | :---------------------- | :--------------------------------------- | :----------- |
| Signature                                 | `theories/sub_derive.v` | `Definition sig`                         |              |
| Definition 4.1 (Sub-derivation)           | `theories/sub_derive.v` | `Definition sub_derive`                  |              |
| One-step reachability relation            | `theories/sub_derive.v` | `Inductive step`                         | Infix `→₁`   |
| Definition 4.2 (Reachability)             | `theories/sub_derive.v` | `Definition reachable`                   | Infix `→∗`   |
| Lemma 4.3                                 | `theories/sub_derive.v` | `Lemma reachable_spec`                   |              |
| Dissimilarity of parse trees              | `theories/ambiguity.v`  | `Definition similar`                     |              |
| Definition 4.4 (Local ambiguity)          | `theories/ambiguity.v`  | `Definition local_amb`                   |              |
| Theorem 4.5                               | `theories/ambiguity.v`  | `Theorem derive_amb_iff_local_amb`       |              |
| Satisfying model                          | `theories/encoding.v`   | `Record model`                           |              |
| The SMT encoding $\Phi(k)$                | `theories/encoding.v`   | `Definition Φ_amb`                       |              |
| Layout constrains encoding $\Phi_\varphi$ | `theories/encoding.v`   | `Variable Φ_app₁, Φ_app₂`                |              |
| Edge relations on LS2NF graph             | `theories/acyclic.v`    | `Inductive succ, prec`                   |              |
| Acyclicity of LS2NF                       | `theories/acyclic.v`    | `Definition acyclic`                     |              |
| Well-foundedness                          | `theories/acyclic.v`    | `Lemma acyclic_prec_wf, acyclic_succ_wf` |              |
| Sub-formula $\Phi_D(k)$                   | `theories/encoding.v`   | `Definition Φ_derive`                    |              |
| Lemma 5.1                                 | `theories/encoding.v`   | `Lemma Φ_derive_spec`                    |              |
| Sub-formula $\Phi_R^\varepsilon(k)$       | `theories/encoding.v`   | `Definition Φ_reach_empty`               |              |
| Lemma 5.3                                 | `theories/encoding.v`   | `Lemma Φ_reach_empty_spec`               |              |
| Sub-formula $\Phi_R^{\not\varepsilon}(k)$ | `theories/encoding.v`   | `Definition Φ_reach_nonempty`            |              |
| Lemma 5.4                                 | `theories/encoding.v`   | `Lemma Φ_reach_nonempty_spec`            |              |
| Choice clause syntax                      | `theories/encoding.v`   | `Inductive choice_clause`                |              |
| Choice clause semantics                   | `theories/encoding.v`   | `Definition Φ_choice_sem`                |              |
| Sub-formula $\Phi_\text{multi}$           | `theories/encoding.v`   | `Definition Φ_multi`                     |              |
| Lemma 5.7                                 | `theories/encoding.v`   | `Lemma Φ_multi_spec`                     |              |
| Theorem 5.9 (Soundness)                   | `theories/encoding.v`   | `Φ_amb_sound`                            |              |
| Theorem 5.10 (Completeness)               | `theories/encoding.v`   | `Φ_amb_complete`                         |              |

This proof artifact contains the following proof files:
- proof/theories/grammar.v: basic definitions about layout-sensitive grammars, including the definition of LS2NF, parse trees, witness judgment, and a "declarative" notion of derivation. 
- proof/theories/derivation.v: an inductive definition of the derivation relation and its equivalence proof to the "declarative" notion defined in `grammar.v`.
- proof/theories/witness.v: a set of helper lemmas for proving the witness judgment by the type of clause.
- proof/theories/sub_derive.v: definition of sub-derivation and lemmas correspond to reachability relation.
- proof/theories/ambiguity.v: the standard notion of ambiguity, our definition of local ambiguity, and their logical equivalence proof.
- proof/theories/acyclic.v: successor and predecessor relations on the graph representation of LS2NF, together with proof of their well-foundedness.
- proof/theories/encoding.v: our SMT encoding with its soundness and completeness proofs (our main theorems).
- proof/theories/acyclic_wf.v: helper lemmas for proving well-foundedness from acyclicity.
- proof/theories/slice.v: helper lemmas for list slicing.
- proof/theories/util.v: other helper lemmas.

Below is a dependency diagram of the proof files: TODO


