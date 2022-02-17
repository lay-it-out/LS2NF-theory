From stdpp Require Import relations list.
From Coq Require Import ssreflect.
From ambig Require Import grammar.

Section derivation.

  Context {Σ N : Type} `{!EqDecision Σ} `{!EqDecision N}.
  Context (G : grammar Σ N).

  Open Scope grammar_scope.

  Inductive derivation : N → sentence Σ → Prop :=
  | derive_ε A :
    A ↦ ε ∈ G →
    derivation A []
  | derive_atom A a p :
    A ↦ atom a ∈ G →
    derivation A [a @ p]
  | derive_unary A B φ w :
    A ↦ unary B φ ∈ G →
    apply₁ φ w = true →
    derivation B w →
    derivation A w
  | derive_binary A Bl Br φ w1 w2 :
    A ↦ binary Bl Br φ ∈ G →
    apply₂ φ w1 w2 = true →
    derivation Bl w1 →
    derivation Br w2 →
    derivation A (w1 ++ w2)
  .

  Lemma derivation_spec A w :
    derivation A w ↔ G ⊨ A => w.
  Proof.
    split.
    - (* -> *)
      induction 1.
      + exists (ε_tree A).
        repeat split. by constructor.
      + exists (token_tree A (a @ p)).
        repeat split. by constructor.
      + destruct IHderivation as [t [? [? ?]]].
        exists (unary_tree A t).
        repeat split => //=. econstructor; naive_solver.
      + destruct IHderivation1 as [t1 [? [? ?]]].
        destruct IHderivation2 as [t2 [? [? ?]]].
        exists (binary_tree A t1 t2).
        repeat split => //; try naive_solver.
        econstructor; naive_solver.
    - (* <- *)
      intros [t [? [? Ht]]].
      generalize dependent w.
      generalize dependent A.
      induction t; inversion Ht; subst => ????.
      all: simpl in *; subst.
      + by constructor.
      + by constructor.
      + eapply derive_unary; eauto.
      + eapply derive_binary; eauto.
  Qed.

  Definition check_derive A w : Prop :=
    (w = [] ∧ A ↦ ε ∈ G) ∨
    (∃ a p, w = [a @ p] ∧ A ↦ atom a ∈ G) ∨
    (∃ B φ, A ↦ unary B φ ∈ G ∧ apply₁ φ w = true ∧ derivation B w) ∨
    (∃ Bl Br φ, A ↦ binary Bl Br φ ∈ G ∧ ∃ w1 w2, w = w1 ++ w2 ∧
      apply₂ φ w1 w2 = true ∧ derivation Bl w1 ∧ derivation Br w2)
    .

  Lemma check_derive_spec A w :
    check_derive A w ↔ derivation A w.
  Proof.
    split.
    - intros [H|[H|[H|H]]].
      + destruct H as [-> ?]. by constructor.
      + destruct H as [a [p [-> ?]]]. by constructor.
      + destruct H as [B [φ [? [? ?]]]]. eapply derive_unary; eauto.
      + destruct H as [Bl [Br [φ [? [w1 [w2 [-> [? [? ?]]]]]]]]]. eapply derive_binary; eauto.
    - inversion 1; subst.
      + by left.
      + right; left. naive_solver.
      + right; right; left. naive_solver.
      + right; right; right. naive_solver.
  Qed.

End derivation.
