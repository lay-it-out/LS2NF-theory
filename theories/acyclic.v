From stdpp Require Import relations.
From Coq Require Import ssreflect.
From ambig Require Import grammar.

Section acyclic.

  Variable Σ N : Type.

  (* On the graph representation of the grammar: direct edge *)
  Inductive succ (G : grammar Σ N) : relation N :=
    | succ_unary A B φ :
      A ↦ unary B φ ∈ G →
      succ G A B
    | succ_left A B E φ :
      A ↦ binary B E φ ∈ G →
      G ⊨ E ⇒ [] →
      succ G A B
    | succ_right A B E φ :
      A ↦ binary E B φ ∈ G →
      G ⊨ E ⇒ [] →
      succ G A B
    .

  (* On graph: do not have non-trivial cycles (a cycle with min length 2) *)
  Definition unit G : Prop :=
    ¬ ∃ A B, A ≠ B ∧ succ G A B ∧ ex_loop (succ G) B.

  (* every grammar can be unitized *)

  (* acyclic *)

  Definition acyclic G : Prop :=
    ¬ ∃ A, ex_loop (succ G) A.

  Axiom acyclic_succ_flip_wf : ∀ G,
    acyclic G → wf (flip (succ G)).

  Axiom acyclic_succ_wf : ∀ G,
    acyclic G → wf (succ G).

End acyclic.

Arguments succ {_} {_}.
Arguments acyclic {_} {_}.
