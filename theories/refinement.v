From stdpp Require Import prelude.
From LS2NF Require Import grammar.
From Coq Require Import ssreflect.

Local Open Scope grammar_scope.

Definition unary_predicate_implication {Σ : Type} (φ' φ : unary_predicate Σ) : Prop :=
  ∀ w, app₁ φ' w = true → app₁ φ w = true.

Notation "φ' →₁ φ" := (unary_predicate_implication φ' φ) (at level 40) : grammar_scope.

Definition binary_predicate_implication {Σ : Type} (φ' φ : binary_predicate Σ) : Prop :=
  ∀ w1 w2, app₂ φ' w1 w2 = true → app₂ φ w1 w2 = true.

Notation "φ' →₂ φ" := (binary_predicate_implication φ' φ) (at level 40) : grammar_scope.

Definition refinement {Σ N : Type} (G' G : grammar Σ N) : Prop :=
  (∀ A, A ↦ ε ∈ G' → A ↦ ε ∈ G) ∧
  (∀ A a, A ↦ atom a ∈ G' → A ↦ atom a ∈ G) ∧
  (∀ A B φ', A ↦ unary B φ' ∈ G' → ∃ φ, A ↦ unary B φ ∈ G ∧ φ' →₁ φ) ∧
  (∀ A B1 B2 φ', A ↦ binary B1 B2 φ' ∈ G' → ∃ φ, A ↦ binary B1 B2 φ ∈ G ∧ φ' →₂ φ).

Notation "G' ≾ G" := (refinement G' G) (at level 40): grammar_scope.

Section refinement.

  Context {Σ N : Type}.
  Implicit Type G : grammar Σ N.

  Lemma refinement_tree G' G t :
    G' ≾ G →
    ✓{G'} t → ✓{G} t.
  Proof.
    intros [? [? [Hu Hb]]] Ht. induction t; inversion Ht; subst; clear Ht.
    - apply valid_ε. eauto.
    - apply valid_token. eauto.
    - edestruct Hu as [φ' [? Hφ']]; eauto.
      eapply valid_unary. 1,2: eauto. by apply Hφ'.
    - edestruct Hb as [φ' [? Hφ']]; eauto.
      eapply valid_binary. 1,2,3: eauto. by apply Hφ'.
  Qed.

  Corollary refinement_witness G' G t A w :
    G' ≾ G →
    t ▷ A ={ G' }=> w →
    t ▷ A ={ G }=> w.
  Proof.
    intros ? [? [? ?]]. repeat split => //.
    eapply refinement_tree; eauto.
  Qed.

End refinement.