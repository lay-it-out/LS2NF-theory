From stdpp Require Import prelude.
From Coq Require Import ssreflect.
From ambig Require Import grammar ambiguity.

Definition clause_loop {Σ N : Type} `{EqDecision N} (α : clause Σ N) A : bool :=
  match α with
  | unary A' _ => bool_decide (A' = A)
  | _ => false
  end.

Definition deloop {Σ N : Type} `{!EqDecision N} (G : grammar Σ N) : grammar Σ N := {|
  start := start G;
  P A := filter (λ α, ¬ bool_decide (clause_loop α A)) (P G A)
|}.

Global Instance valid_decidable Σ N (G : grammar Σ N) t : Decision (✓{G} t).
Admitted.

Lemma deloop_tree_invalid {Σ N} `{!EqDecision N} (G : grammar Σ N) t :
  ✓{G} t →
  ¬ ✓{deloop G} t →
  ∃ A φ w, G ⊢ A ↦ unary A φ ∧ G ⊨ A ⇒ w ∧ (w ≠ [] → φ w).
Proof.
  induction t as [| A [a p] | A t IHt |?].
  all: inversion 1; subst => Hnot.
  - exfalso. apply Hnot. econstructor => /=.
    eapply elem_of_list_filter. naive_solver.
  - exfalso. apply Hnot. econstructor => /=.
    eapply elem_of_list_filter. naive_solver.
  - destruct (decide (A = root t)) as [->|].
    + exists (root t), φ, (sentence_of t).
      repeat split => //. exists t. by repeat split.
    + apply IHt; first done. move => ?.
      have ? : ✓{deloop G} unary_tree A t.
      { econstructor; eauto. eapply elem_of_list_filter. naive_solver. }
      contradiction.
  - destruct (decide (✓{deloop G} t1)); first destruct (decide (✓{deloop G} t2)).
    + (* both valid *)
      exfalso. apply Hnot. econstructor; eauto.
      eapply elem_of_list_filter. naive_solver.
    + (* t2 not valid *) by apply IHt2.
    + (* t1 not valid *) by apply IHt1.
Qed.
