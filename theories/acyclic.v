From stdpp Require Import relations finite.
From Coq Require Import ssreflect.
From LS2NF Require Import grammar acyclic_wf.

Section acyclic.

  Context {Σ N : Type} `{!EqDecision N} `{!Finite N}.
  Context (G : grammar Σ N).

  Open Scope grammar_scope.

  (* This relation corresponds to directed edges on the graph representation
     of a grammar. *)
  Inductive succ : relation N :=
    | succ_unary A B φ :
      A ↦ unary B φ ∈ G →
      succ A B
    | succ_left A B E φ :
      A ↦ binary B E φ ∈ G →
      G ⊨ E => [] →
      succ A B
    | succ_right A B E φ :
      A ↦ binary E B φ ∈ G →
      G ⊨ E => [] →
      succ A B
    .

  (* The directed edges reversed. *)
  Definition prec : relation N := flip succ.

  (* A grammar is acyclic if its graph is acyclic, i.e.
     the `succ` relation is an acyclic relation. *)
  Definition acyclic : Prop := acyclic succ.

  (* Both `prec` and `succ` are well-founded for acyclic grammars. *)
  Lemma acyclic_prec_wf :
    acyclic → wf prec.
  Proof. intros. eapply finite_acyclic_flip_wf; eauto. Qed.
  Lemma acyclic_succ_wf :
    acyclic → wf succ.
  Proof. intros. eapply finite_acyclic_wf; eauto. Qed.

End acyclic.
