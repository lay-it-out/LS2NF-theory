From stdpp Require Import relations list.
From Coq Require Import ssreflect.

Section grammar.

  (* token, sentence *)

  Variable Σ : Type.
  Context `{EqDecision Σ}.

  Record token := {
    letter : Σ;
    pos : nat (* line number *) * nat (* column number *);
  }.

  Arguments letter {_}.
  Arguments pos {_}.

  Declare Scope grammar_scope.
  Local Open Scope grammar_scope.

  Notation "a @ p" := {|
    letter := a;
    pos := p;
  |} (at level 40).

  Definition sentence : Type := list token.

  Global Instance token_eq_dec : EqDecision token.
  Proof.
    intros [a1 p1] [a2 p2].
    destruct (decide (a1 = a2 ∧ p1 = p2)); [left | right]; naive_solver.
  Qed.

  (* nonterminals *)

  Variable N : Type.
  Context `{EqDecision N}.

  (* layout-free clauses *)

  Inductive lf_clause : Type :=
    | lf_ε
    | lf_atom (a : Σ)
    | lf_unary (A : N)
    | lf_binary (Al Ar : N)
    .

  Definition check_lf_clause_eq α β : bool :=
    match α, β with
    | lf_ε, lf_ε => true
    | lf_atom a, lf_atom b => bool_decide (a = b)
    | lf_unary A, lf_unary A' => bool_decide (A = A')
    | lf_binary Al Ar, lf_binary Al' Ar' =>
      bool_decide (Al = Al') && bool_decide (Ar = Ar')
    | _, _ => false
    end.

  Lemma check_lf_clause_eq_spec α β :
    check_lf_clause_eq α β = true ↔ α = β.
  Proof.
    destruct α; destruct β => //=.
    all: try rewrite !andb_true_iff.
    all: rewrite !bool_decide_eq_true.
    all: naive_solver.
  Qed.

  Global Instance lf_clause_eq_dec : EqDecision lf_clause.
  Proof.
    intros α β.
    have ? := check_lf_clause_eq_spec α β.
    destruct (check_lf_clause_eq α β); [left | right]; naive_solver.
  Qed.

  (* layout predicates *)

  Definition unary_predicate : Type :=
    {p : sentence → bool & p [] = true}.
  Definition apply₁ (φ : unary_predicate) := projT1 φ.

  Definition binary_predicate : Type :=
    {p : sentence → sentence → bool & ∀ w1 w2, w1 = [] ∨ w2 = [] → p w1 w2 = true}.
  Definition apply₂ (φ : binary_predicate) := projT1 φ.

  (* grammar *)

  Record grammar := {
    (* start symbol *)
    start : N;
    (* productions *)
    lf_clauses : N → list lf_clause;
    lf_clauses_no_dup : ∀ A, NoDup (lf_clauses A);
    unary_clause_predicate : N → N → unary_predicate;
    binary_clause_predicate : N → N → N → binary_predicate;
  }.

  Implicit Type G : grammar.

  (* clauses and productions *)

  Inductive clause : Type :=
    | ε : clause
    | atom : Σ → clause
    | unary : N → unary_predicate → clause
    | binary : N → N → binary_predicate → clause
    .

  Definition clauses G A : list clause :=
    (λ α, match α with
    | lf_ε => ε
    | lf_atom a => atom a
    | lf_unary B => unary B (unary_clause_predicate G A B)
    | lf_binary Bl Br => binary Bl Br (binary_clause_predicate G A Bl Br)
    end) <$> lf_clauses G A.

  Inductive production : Type :=
    mk_production : N → clause → production.

  Notation "A ↦ α" := (mk_production A α) (at level 40).

  Global Instance production_elem_of_grammar : ElemOf production grammar := λ p G,
    match p with
    | mk_production A α => α ∈ clauses G A
    end.

  (* So that one can use notation "A ↦ α ∈ G" *)

  (* parsing *)

  Inductive tree : Type :=
    | ε_tree : N → tree
    | token_tree : N → token → tree
    | unary_tree : N → tree → tree
    | binary_tree : N → tree → tree → tree
    .

  Definition root t : N :=
    match t with
    | ε_tree R => R
    | token_tree R _ => R
    | unary_tree R _ => R
    | binary_tree R _ _ => R
    end.

  Fixpoint word t : sentence :=
    match t with
    | ε_tree _ => []
    | token_tree _ tk => [tk]
    | unary_tree _ t' => word t'
    | binary_tree _ t1 t2 => word t1 ++ word t2
    end.

  Fixpoint check_tree_eq t1 t2 : bool :=
    match t1, t2 with
    | ε_tree A, ε_tree A' => bool_decide (A = A')
    | token_tree A tk1, token_tree A' tk2 => bool_decide (A = A' ∧ tk1 = tk2)
    | unary_tree A t1, unary_tree A' t2 =>
      bool_decide (A = A') && check_tree_eq t1 t2
    | binary_tree A tA1 tB1, binary_tree A' tA2 tB2 =>
      bool_decide (A = A') && check_tree_eq tA1 tA2 && check_tree_eq tB1 tB2
    | _, _ => false
    end.

  Lemma check_tree_eq_spec t1 t2 :
    check_tree_eq t1 t2 = true ↔ t1 = t2.
  Proof.
    generalize dependent t2.
    induction t1; destruct t2 => //=.
    all: try rewrite !andb_true_iff.
    all: rewrite !bool_decide_eq_true.
    all: naive_solver.
  Qed.

  Global Instance tree_eq_dec : EqDecision tree.
  Proof.
    intros t1 t2.
    have ? := check_tree_eq_spec t1 t2.
    destruct (check_tree_eq t1 t2); [left | right]; naive_solver.
  Qed.

  Inductive tree_valid G : tree → Prop :=
    | valid_ε A :
      A ↦ ε ∈ G →
      tree_valid G (ε_tree A)
    | valid_token A a p :
      A ↦ atom a ∈ G →
      tree_valid G (token_tree A (a @ p))
    | valid_unary A t' φ :
      A ↦ unary (root t') φ ∈ G →
      tree_valid G t' →
      apply₁ φ (word t') = true →
      tree_valid G (unary_tree A t')
    | valid_binary A t1 t2 φ :
      A ↦ binary (root t1) (root t2) φ ∈ G →
      tree_valid G t1 →
      tree_valid G t2 →
      apply₂ φ (word t1) (word t2) = true →
      tree_valid G (binary_tree A t1 t2)
    .

  Notation "✓{ G } t" := (tree_valid G t) (at level 40, format "'✓{' G '}'  t").

  Definition tree_witness G t A w :=
    root t = A ∧ word t = w ∧ ✓{G} t.

  Notation "t ▷ A ={ G }=> w" := (tree_witness G t A w) (at level 40).

  (* Fixpoint check_tree_valid G (t : tree Σ N) : bool :=
    match t with
    | ε_tree A => bool_decide (A ↦ ε ∈ G)
    (* | token_tree A tk => atom_productions G A (letter tk)
    | unary_tree A t' =>
      match unary_productions G A (root t') with
      | Some φ => tree_valid G t' && φ (word t')
      | None => false
      end
    | binary_tree A t1 t2 =>
      match binary_productions G A (root t1) (root t2) with
      | Some φ => tree_valid G t1 && tree_valid G t2 && φ (word t1) (word t2)
      | None => false
      end *)
    | _ => false
    end. *)
(* 
  Global Instance ParseTree_tree : ParseTree tree := {|
    root := root;
    word := word;
    valid := tree_valid;
  |}. *)

  (* derivation *)

  Definition derive G A w : Prop :=
    ∃ t, t ▷ A ={G}=> w.

  Notation "G ⊨ A ⇒ w" := (derive G A w) (at level 65).

  (* Lemma derive_ε G A :
    A ↦ ε ∈ G →
    G ⊨ A ⇒ [].
  Proof.
    intros. exists (ε_tree A).
    repeat split. by constructor.
  Qed.

  Lemma derive_atom G A a p :
    A ↦ atom a ∈ G →
    G ⊨ A ⇒ [a @ p].
  Proof.
    intros. exists (token_tree A (a @ p)).
    repeat split. by constructor.
  Qed.

  Lemma derive_unary G A B φ w :
    A ↦ unary B φ ∈ G →
    apply₁ φ w = true →
    G ⊨ B ⇒ w →
    G ⊨ A ⇒ w.
  Proof.
    intros ? ? [t [? [? ?]]]. exists (unary_tree A t).
    repeat split => //. econstructor; naive_solver.
  Qed.

  Lemma derive_binary G A Bl Br φ w1 w2 :
    A ↦ binary Bl Br φ ∈ G →
    apply₂ φ w1 w2 = true →
    G ⊨ Bl ⇒ w1 →
    G ⊨ Br ⇒ w2 →
    G ⊨ A ⇒ w1 ++ w2.
  Proof.
    intros ? ? [t1 [? [? ?]]] [t2 [? [? ?]]].
    exists (binary_tree A t1 t2).
    repeat split; try naive_solver.
    econstructor; naive_solver.
  Qed. *)

  (* nullability *)

  Definition nullable G (A : N) : bool.
  Admitted.

  Fact nullable_spec G A :
    nullable G A = true ↔ G ⊨ A ⇒ [].
  Admitted.

  Global Instance nullable_dec G A : Decision (G ⊨ A ⇒ []).
  Proof.
    have ? := nullable_spec G A.
    destruct (nullable G A); [left | right]; naive_solver.
  Qed.

  (* standard notion of ambiguity *)

  Definition derive_amb G A w : Prop :=
    ∃ t1 t2, t1 ▷ A ={G}=> w ∧ t2 ▷ A ={G}=> w ∧ t1 ≠ t2.

  Definition amb G :=
    ∃ w, derive_amb G (start G) w.

End grammar.

Arguments letter {_}.
Arguments pos {_}.

Arguments start {_} {_}.

Arguments ε {_} {_}.
Arguments atom {_} {_}.
Arguments unary {_} {_}.
Arguments binary {_} {_}.

Arguments clauses {_} {_}.
Arguments mk_production {_} {_}.

Arguments apply₁ {_}.
Arguments apply₂ {_}.

Arguments ε_tree {_} {_}.
Arguments token_tree {_} {_}.
Arguments unary_tree {_} {_}.
Arguments binary_tree {_} {_}.

Arguments root {_} {_}.
Arguments word {_} {_}.
Arguments tree_valid {_} {_}.
Arguments derive {_} {_}.
Arguments nullable {_} {_} {_} {_}.
Arguments tree_witness {_} {_}.

Notation "a @ p" := {|
  letter := a;
  pos := p;
|} (at level 40).

Notation "A ↦ α" := (mk_production A α) (at level 40).

Notation "✓{ G } t" := (tree_valid G t) (at level 40, format "'✓{' G '}'  t").

Notation "G ⊨ A ⇒ w" := (derive G A w) (at level 65).

Notation "t ▷ A ={ G }=> w" := (tree_witness G t A w) (at level 40).

Arguments derive_amb {_} {_}.
Arguments amb {_} {_}.
