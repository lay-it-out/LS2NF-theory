From stdpp Require Import prelude.
From ambig Require Import grammar.

(* standard notion of ambiguity *)

Definition sentence_ambiguous {Σ N : Type} (G : grammar Σ N) (w : sentence Σ) : Prop :=
  ∃ t1 t2 : tree Σ N,
    (t1 ▷ (start G) ={G}=> w) ∧ (t2 ▷ (start G) ={G}=> w) ∧ t1 ≠ t2.

Definition ambiguous {Σ N : Type} (G : grammar Σ N) :=
  ∃ w, sentence_ambiguous G w.

(* bounded ambiguity *)

Definition differ_on_first_level {Σ N : Type} (t1 t2 : tree Σ N) : Prop :=
  match t1, t2 with
  | ε_tree _, ε_tree _ => False
  | token_tree _ tk1, token_tree _ tk2 => tk1 ≠ tk2
  | unary_tree _ t1', unary_tree _ t2' => root t1' ≠ root t2'
  | binary_tree _ tA1 tB1, binary_tree _ tA2 tB2 => root tA1 ≠ root tA2 ∨ root tB1 ≠ root tB2
  | _, _ => True (* constructor differs *)
  end.

Definition bounded_ambiguous {Σ N : Type} (G : grammar Σ N) : Prop :=
  ∃ A w t1, (t1 ▷ A ={G}=> w) ∧
    ∃ t2, (t2 ▷ A ={G}=> w) ∧ differ_on_first_level t1 t2.
