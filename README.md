# Layout Sensitive Binary Normal Form (LS2NF) Theories

[![Build][build-badge]][build-link]

[build-badge]: https://github.com/lay-it-out/LS2NF-theory/actions/workflows/build.yml/badge.svg?branch=main
[build-link]: https://github.com/lay-it-out/LS2NF-theory/actions/workflows/build.yml

This repository contains the Coq formulation on LS2NF, its properties, and a sound and complete SMT encoding for checking its bounded ambiguity.

## Build

### Via Nix

```sh
nix build
```

This will download all dependencies and compile the Coq code. If no error messages show, then the theorems are all machine-checked.

### Via Docker

```sh
docker build .
```

This will create a Docker image of NixOS with the above `nix build` command executed.

## Step Into the Code

Type `nix develop` to enter the development shell, which contains all the dependent packages. Then start your favorite Coq IDE to step into the code, for instance, using VS code:
```sh
(nix:coq8.17-LS2NF-dev-env) $ code .
```

## Paper-to-Artifact Correspondence Guide

This repository supports the results shown in the paper "Automated Ambiguity Detection in Layout-Sensitive Grammars". All the definitions and theorems mentioned in §4 and §5 are formulated. The main theorems are the soundness (Theorem 5.9) and completeness (Theorem 5.10) of our SMT encoding (§5).

In the order in which the definitions and theorems appear in the paper, the following tables list their counterparts in the Coq code (under `theories/` folder). The first table lists the definitions mentioned in §3:

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

The second table lists the definitions and theorems mentioned in §4 and §5:

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

### Dependency

This proof relies on [stdpp](https://gitlab.mpi-sws.org/iris/stdpp), an extended "standard library" for Coq. We find the lemmas on lists, relations, and sorting theories useful to our proof.

### Folder Structure

The Coq files are all located in `theories/` folder:

| File           | Content/Purpose                                                  |
| :------------- | :--------------------------------------------------------------- |
| `acyclic_wf.v` | Helper definitions and lemmas for proving well-foundedness       |
| `acyclic.v`    | Acyclicity and well-foundedness                                  |
| `ambiguity.v`  | Local ambiguity with its equivalence to the standard ambiguity   |
| `derivation.v` | Helper lemmas for proving derivation                             |
| `encoding.v`   | SMT encoding with its soundness and completeness proofs          |
| `grammar.v`    | Preliminary definitions on LS2NF and parsing                     |
| `slice.v`      | Helper lemmas for list slicing                                   |
| `sub_derive.v` | Sub-derivation, reachability, and their correlation              |
| `util.v`       | Other helper definitions and lemmas                              |
| `witness.v`    | Helper lemmas for proving witness judgment                       |

### Justification of Assumptions

One assumption we made: the alphabet (or the terminal set) of an LS2NF shall be nonempty. We introduced this via type class constraint `{!Inhabited Σ}` at line 11 of file `encoding.v`. This makes sense because a language with an empty alphabet is trivially empty and thus not interesting at all, though we could elide this by defining `Definition encode` differently (but this will take invaluable efforts).

The other type class constraints are indeed true:
- `{!EqDecision Σ}`: one can decide if two terminals are equal or not;
- `{!EqDecision N}`: one can decide if two nonterminals are equal or not;
- `{!Finite N}`: the nonterminal set is finite.

The encoding of layout constraints is left abstract in `encoding.v` because this proof artifact aims to show the soundness and completeness of a *generic* SMT encoding---generic to any user-specified layout constraints. The definition of those layout constraints shall be regarded as a premise of the main theorems.

The above are all the assumptions we made. To check it automatically, either:
- launch `encoding.v` in your IDE, uncomment the two `Print Assumptions` commands at the end, and step into them to see the outputs; or
- uncomment the two `Print Assumptions` commands at the end of `encoding.v`, save the file, execute `nix develop`, and in the new shell type `make` to see the output messages.
