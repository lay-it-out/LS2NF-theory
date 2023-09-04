From stdpp Require Import relations finite.
From Coq Require Import ssreflect.
From LS2NF Require Import grammar acyclic_wf.

(** * Acyclicity of LS2NF *)

Section acyclic.

  Context {Σ N : Type} `{!EqDecision N}.
  Context (G : grammar Σ N).

  Open Scope grammar_scope.

  (** Relation [succ] corresponds to the directed edges on the graph representation of an LS2NF. *)
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

  (** Relation [prec] is the reverse of [succ]. *)
  Definition prec : relation N := flip succ.

  (** A grammar is _acyclic_ if its graph is acyclic, i.e., the [succ] relation is an acyclic
      relation. *)
  Definition acyclic : Prop := rel_acyclic succ.

  Context `{!Finite N}.

  (** Both [prec] and [succ] are well-founded relations on acyclic grammars. *)
  Lemma acyclic_prec_wf :
    acyclic → wf prec.
  Proof. intros. eapply acyclic_flip_wf; eauto. Qed.
  Lemma acyclic_succ_wf :
    acyclic → wf succ.
  Proof. intros. eapply acyclic_wf; eauto. Qed.

End acyclic.
