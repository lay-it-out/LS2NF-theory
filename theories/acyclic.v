From stdpp Require Import relations finite.
From Coq Require Import ssreflect.
From ambig Require Import grammar acyclic_wf.

Section acyclic.

  Context {Σ N : Type} `{Finite N} (G : grammar Σ N).

  (* On the graph representation of the grammar: direct edge *)
  Inductive succ : relation N :=
    | succ_unary A B φ :
      A ↦ unary B φ ∈ G →
      succ A B
    | succ_left A B E φ :
      A ↦ binary B E φ ∈ G →
      G ⊨ E ⇒ [] →
      succ A B
    | succ_right A B E φ :
      A ↦ binary E B φ ∈ G →
      G ⊨ E ⇒ [] →
      succ A B
    .

  Definition prec : relation N := flip succ.

  (* acyclic grammar *)

  Definition acyclic : Prop := acyclic succ.

  Lemma acyclic_succ_flip_wf :
    acyclic → wf (flip succ).
  Proof.
    intros. eapply acyclic_flip_wf; eauto.
  Qed.

  Lemma acyclic_succ_wf :
    acyclic → wf succ.
  Proof.
    intros. eapply acyclic_wf; eauto.
  Qed.

End acyclic.
