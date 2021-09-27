From stdpp Require Import relations list.
From Coq Require Import ssreflect.

(* sentence *)

Record token (Σ : Type) := {
  letter : Σ;
  pos : nat (* line number *) * nat (* column number *);
}.

Arguments letter {_}.
Arguments pos {_}.

Notation "a @ p" := {|
  letter := a;
  pos := p;
|} (at level 40).

Definition sentence (Σ : Type) : Type := list (token Σ).

(* predicate should be decidable *)

Definition unary_predicate (Σ : Type) : Type := sentence Σ → bool.
Definition binary_predicate (Σ : Type) : Type := sentence Σ → sentence Σ → bool.

(* grammar *)

Record grammar (Σ N : Type) := {
  start : N;
  ε_productions : N → bool;
  atom_productions : N → Σ → bool;
  unary_productions : N → N → option (unary_predicate Σ);
  binary_productions : N → N → N → option (binary_predicate Σ);
  unary_predicate_axiom : ∀ φ : unary_predicate Σ, φ [];
  binary_predicate_axiom : ∀ (φ : binary_predicate Σ) w1 w2,
    (w1 = [] ∨ w2 = []) → φ w1 w2;
}.

Arguments start {_} {_}.
Arguments ε_productions {_} {_}.
Arguments atom_productions {_} {_}.
Arguments unary_productions {_} {_}.
Arguments binary_productions {_} {_}.
Arguments unary_predicate_axiom {_} {_}.
Arguments binary_predicate_axiom {_} {_}.

Inductive clause (Σ N : Type) : Type :=
  | ε : clause Σ N
  | atom : Σ → clause Σ N
  | unary : N → unary_predicate Σ → clause Σ N
  | binary : N → N → binary_predicate Σ → clause Σ N
  .

Arguments ε {_} {_}.
Arguments atom {_} {_}.
Arguments unary {_} {_}.
Arguments binary {_} {_}.

(* NOTE

One can also define the production set of a grammar as a function from N to list (clause Σ N).

But this definition has two disadvantages:
1. To show that (A ↦ α ∈ G) is decidable, we need to show that predicates are eq decidable, which is not so obvious (though in practice the predicates are taken from a predefined set)
2. This definition fails to reject productions with conflicting predicates, e.g. A ↦ B offside and A ↦ B same_line.
*)

Inductive production (Σ N : Type) : Type :=
  mk_production : N → clause Σ N → production Σ N.

Arguments mk_production {_} {_}.

Notation "A ↦ α" := (mk_production A α) (at level 40).

Global Instance production_elem_of_grammar Σ N : ElemOf (production Σ N) (grammar Σ N) := λ p G,
  match p with
  | mk_production A ε => ε_productions G A
  | mk_production A (atom a) => atom_productions G A a
  | mk_production A (unary B φ) => unary_productions G A B = Some φ
  | mk_production A (binary Bl Br φ) => binary_productions G A Bl Br = Some φ
  end.

(* So that one can use notation "A ↦ α ∈ G" *)

Lemma unary_predicate_unique {Σ N} (G : grammar Σ N) A B φ1 φ2 :
  A ↦ unary B φ1 ∈ G →
  A ↦ unary B φ2 ∈ G →
  φ1 = φ2.
Proof. congruence. Qed.

Lemma binary_predicate_unique {Σ N} (G : grammar Σ N) A Bl Br φ1 φ2 :
  A ↦ binary Bl Br φ1 ∈ G →
  A ↦ binary Bl Br φ2 ∈ G →
  φ1 = φ2.
Proof. congruence. Qed.

(* interfaces for a parse tree *)

Class ParseTree (Σ N : Type) (tree : Type → Type → Type) := {
  root : tree Σ N → N;
  word : tree Σ N → sentence Σ;
  (* validity is decidable *)
  valid : grammar Σ N → tree Σ N → bool;
  witness G t A w := root t = A ∧ word t = w ∧ valid G t;
}.

Notation "✓{ G } t" := (valid G t) (at level 40, format "'✓{' G '}'  t").

Notation "t ▷ A ={ G }=> w" := (witness G t A w) (at level 40).

(* parsing *)

Inductive tree (Σ N : Type) : Type :=
  | ε_tree : N → tree Σ N
  | token_tree : N → token Σ → tree Σ N
  | unary_tree : N → tree Σ N → tree Σ N
  | binary_tree : N → tree Σ N → tree Σ N → tree Σ N
  .

Arguments ε_tree {_} {_}.
Arguments token_tree {_} {_}.
Arguments unary_tree {_} {_}.
Arguments binary_tree {_} {_}.

Definition tree_root {Σ N : Type} (t : tree Σ N) : N :=
  match t with
  | ε_tree R => R
  | token_tree R _ => R
  | unary_tree R _ => R
  | binary_tree R _ _ => R
  end.

Fixpoint tree_word {Σ N : Type} (t : tree Σ N) : sentence Σ :=
  match t with
  | ε_tree _ => []
  | token_tree _ tk => [tk]
  | unary_tree _ t' => tree_word t'
  | binary_tree _ t1 t2 => tree_word t1 ++ tree_word t2
  end.

Fixpoint tree_valid {Σ N : Type} (G : grammar Σ N) (t : tree Σ N) : bool :=
  match t with
  | ε_tree A => ε_productions G A
  | token_tree A tk => atom_productions G A (letter tk)
  | unary_tree A t' =>
    match unary_productions G A (tree_root t') with
    | Some φ => tree_valid G t' && φ (tree_word t')
    | None => false
    end
  | binary_tree A t1 t2 =>
    match binary_productions G A (tree_root t1) (tree_root t2) with
    | Some φ => tree_valid G t1 && tree_valid G t2 && φ (tree_word t1) (tree_word t2)
    | None => false
    end
  end.

Global Instance ParseTree_tree Σ N : ParseTree Σ N tree := {|
  root := tree_root;
  word := tree_word;
  valid := tree_valid;
|}.

Lemma Is_true_andb (b1 b2 : bool) :
  b1 ∧ b2 → b1 && b2.
Proof.
  naive_solver.
Qed.

Lemma valid_ε_tree {Σ N : Type} (G : grammar Σ N) A :
  A ↦ ε ∈ G →
  ✓{G} ε_tree A.
Proof.
  naive_solver.
Qed.

Lemma valid_token_tree {Σ N : Type} (G : grammar Σ N) A tk :
  A ↦ atom (letter tk) ∈ G →
  ✓{G} token_tree A tk.
Proof.
  naive_solver.
Qed.

Lemma valid_unary_tree {Σ N : Type} (G : grammar Σ N) A φ t :
  A ↦ unary (root t) φ ∈ G →
  φ (word t) →
  ✓{G} t →
  ✓{G} unary_tree A t.
Proof.
  move => HA ? ? /=.
  rewrite HA. naive_solver.
Qed.

Lemma valid_binary_tree {Σ N : Type} (G : grammar Σ N) A φ t1 t2 :
  A ↦ binary (root t1) (root t2) φ ∈ G →
  φ (word t1) (word t2) →
  ✓{G} t1 →
  ✓{G} t2 →
  ✓{G} binary_tree A t1 t2.
Proof.
  move => HA ? ? ? /=.
  rewrite HA. naive_solver.
Qed.

Lemma valid_ε_tree_inv {Σ N : Type} (G : grammar Σ N) A :
  ✓{G} ε_tree A →
  A ↦ ε ∈ G.
Proof.
  naive_solver.
Qed.

Lemma valid_token_tree_inv {Σ N : Type} (G : grammar Σ N) A tk :
  ✓{G} token_tree A tk →
  A ↦ atom (letter tk) ∈ G.
Proof.
  naive_solver.
Qed.

Lemma valid_unary_tree_inv {Σ N : Type} (G : grammar Σ N) A t :
  ✓{G} unary_tree A t →
  ∃ φ, A ↦ unary (root t) φ ∈ G ∧ φ (word t) ∧ ✓{G} t.
Proof.
  simpl. case_match; naive_solver.
Qed.

Lemma valid_binary_tree_inv {Σ N : Type} (G : grammar Σ N) A t1 t2 :
  ✓{G} binary_tree A t1 t2 →
  ∃ φ, A ↦ binary (root t1) (root t2) φ ∈ G ∧ φ (word t1) (word t2) ∧
    ✓{G} t1 ∧ ✓{G} t2.
Proof.
  simpl. case_match; naive_solver.
Qed.

(* derivation *)

Definition derive {Σ N : Type} (G : grammar Σ N) (A : N) (w : sentence Σ) : Prop :=
  ∃ (t : tree Σ N), witness G t A w.

Notation "G ⊨ A ⇒ w" := (derive G A w) (at level 65).

Lemma derive_ε {Σ N : Type} (G : grammar Σ N) A :
  A ↦ ε ∈ G →
  G ⊨ A ⇒ [].
Proof.
  intros. exists (ε_tree A).
  repeat split. by apply valid_ε_tree.
Qed.

Lemma derive_atom {Σ N : Type} (G : grammar Σ N) A a p :
  A ↦ atom a ∈ G →
  G ⊨ A ⇒ [a @ p].
Proof.
  intros. exists (token_tree A (a @ p)).
  repeat split. by apply valid_token_tree.
Qed.

Lemma derive_unary {Σ N : Type} (G : grammar Σ N) A B φ w :
  A ↦ unary B φ ∈ G →
  φ w →
  G ⊨ B ⇒ w →
  G ⊨ A ⇒ w.
Proof.
  intros ? ? [t [? [? ?]]]. exists (unary_tree A t).
  repeat split => //. eapply valid_unary_tree; naive_solver.
Qed.

Lemma derive_binary {Σ N : Type} (G : grammar Σ N) A Bl Br φ w1 w2 :
  A ↦ binary Bl Br φ ∈ G →
  φ w1 w2 →
  G ⊨ Bl ⇒ w1 →
  G ⊨ Br ⇒ w2 →
  G ⊨ A ⇒ w1 ++ w2.
Proof.
  intros ? ? [t1 [? [? ?]]] [t2 [? [? ?]]].
  exists (binary_tree A t1 t2).
  repeat split; try naive_solver.
  eapply valid_binary_tree; naive_solver.
Qed.

(* nullability *)

Definition nullable {Σ N : Type} (G : grammar Σ N) (A : N) : bool.
Admitted.

Fact nullable_spec {Σ N : Type} (G : grammar Σ N) A :
  nullable G A → G ⊨ A ⇒ [].
Admitted.

(* standard notion of ambiguity *)

Definition derive_amb {Σ N : Type} (G : grammar Σ N) (A : N) (w : sentence Σ) : Prop :=
  ∃ t1 t2 : tree Σ N, t1 ▷ A ={G}=> w ∧ t2 ▷ A ={G}=> w ∧ t1 ≠ t2.

Definition amb {Σ N : Type} (G : grammar Σ N) :=
  ∃ w, derive_amb G (start G) w.
