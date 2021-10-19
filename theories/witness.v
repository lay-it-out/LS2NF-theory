From stdpp Require Import relations list.
From Coq Require Import ssreflect.
From ambig Require Import grammar.

Section witness.

  Context {Σ N : Type} `{EqDecision Σ} `{EqDecision N}.
  Context (G : grammar Σ N).

  Lemma witness_ε A :
    A ↦ ε ∈ G →
    ε_tree A ▷ A ={ G }=> [].
  Admitted.

  Lemma witness_atom A a p :
    A ↦ atom a ∈ G →
    token_tree A (a @ p) ▷ A ={ G }=> [a @ p].
  Admitted.

  Lemma witness_unary A B φ t w :
    A ↦ unary B φ ∈ G →
    unary_tree A t ▷ A ={G}=> w ↔
    t ▷ B ={G}=> w ∧ apply₁ φ w = true.
  Admitted.

  Lemma witness_binary A Bl Br φ t1 t2 w1 w2 :
    A ↦ binary Bl Br φ ∈ G →
    binary_tree A t1 t2 ▷ A ={G}=> (w1 ++ w2) ↔
    t1 ▷ Bl ={G}=> w1 ∧ t2 ▷ Br ={G}=> w2 ∧ apply₂ φ w1 w2 = true.
  Admitted.

End witness.