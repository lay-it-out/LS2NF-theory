From stdpp Require Import relations list.
From Coq Require Import ssreflect.
From LS2NF Require Import grammar.

Section witness.

  Context {Σ N : Type} `{!EqDecision Σ} `{!EqDecision N}.
  Context (G : grammar Σ N).

  Open Scope grammar_scope.

  Lemma witness_ε A :
    A ↦ ε ∈ G →
    ε_tree A ▷ A ={ G }=> [].
  Proof.
    intros. repeat split. by constructor.
  Qed.

  Lemma witness_atom A a p :
    A ↦ atom a ∈ G →
    token_tree A (a @ p) ▷ A ={ G }=> [a @ p].
  Proof.
    intros. repeat split. by constructor.
  Qed.

  Lemma witness_unary A φ t w :
    A ↦ unary (root t) φ ∈ G →
    unary_tree A t ▷ A ={G}=> w ↔
    t ▷ root t ={G}=> w ∧ app₁ φ w = true.
  Proof.
    intros Hp. split.
    - intros [? [? Ht]]. simpl in *. invert Ht.
      eapply unary_clause_predicate_unique in Hp; eauto.
      split => //. naive_solver.
    - intros [[? [? ?]] ?]. subst. repeat split => //. econstructor; eauto.
  Qed.

  Lemma witness_binary A φ t1 t2 w2 :
    A ↦ binary (root t1) (root t2) φ ∈ G →
    binary_tree A t1 t2 ▷ A ={G}=> (word t1 ++ w2) ↔
    t1 ▷ root t1 ={G}=> word t1 ∧ t2 ▷ root t2 ={G}=> w2 ∧ app₂ φ (word t1) w2 = true.
  Proof.
    intros Hp. split.
    - intros [? [? Ht]]. simpl in *. invert Ht.
      eapply binary_clause_predicate_unique in Hp; eauto.
      repeat split => //; naive_solver.
    - intros [[? [? ?]] [[? [? ?]] ?]]. subst. repeat split => //. econstructor; eauto.
  Qed.

End witness.