From stdpp Require Import relations sorting.
From Coq Require Import ssreflect.

Declare Scope grammar_scope.
Local Open Scope grammar_scope.

(** * Sentences *)

(** Positioned token: a terminal/token with its position in source file. *)
Record pos_token (Σ : Type) := {
  token : Σ;
  pos : nat (* line number *) * nat (* column number *);
}.

Arguments token {_}.
Arguments pos {_}.

Notation "a @ p" := {|
  token := a;
  pos := p;
|} (at level 40) : grammar_scope.

Global Instance pos_token_eq_dec Σ `{!EqDecision Σ} : EqDecision (pos_token Σ).
Proof.
  intros [a1 p1] [a2 p2].
  destruct (decide (a1 = a2 ∧ p1 = p2)); [left | right]; naive_solver.
Qed.

(** An ascending order for [pos_token]: either the line number is increasing, or the column number
    is increasing (when lines are equal). *)
Definition pos_token_lt (Σ : Type) : relation (pos_token Σ) := λ pt1 pt2,
  match pos pt1, pos pt2 with (x1, y1), (x2, y2) =>
    (x1 < x2) ∨ (x1 = x2 ∧ y1 < y2)
  end.

Global Instance pos_token_lt_trans Σ : Transitive (pos_token_lt Σ).
Proof.
  intros [? [? ?]] [? [? ?]] [? [? ?]].
  unfold pos_token_lt. simpl. lia.
Qed.

(** In a layout-sensitive grammar, a _sentence_ is a sequence of positioned tokens. *)
Definition sentence (Σ : Type) : Type := list (pos_token Σ).

(** Well-formedness: the positions of the tokens are in an ascending order. *)
Definition well_formed {Σ : Type} (w : sentence Σ) : Prop :=
  Sorted (pos_token_lt Σ) w.

(** * LS2NF *)

(** Layout-free clauses, essentially the clauses of CFG's binary normal form. *)
Inductive lf_clause (Σ N : Type) : Type :=
  | lf_ε
  | lf_atom (a : Σ)
  | lf_unary (A : N)
  | lf_binary (Al Ar : N)
  .

Arguments lf_ε {_} {_}.
Arguments lf_atom {_} {_}.
Arguments lf_unary {_} {_}.
Arguments lf_binary {_} {_}.

Definition check_lf_clause_eq {Σ N} `{!EqDecision Σ} `{!EqDecision N} (α β : lf_clause Σ N) : bool :=
  match α, β with
  | lf_ε, lf_ε => true
  | lf_atom a, lf_atom b => bool_decide (a = b)
  | lf_unary A, lf_unary A' => bool_decide (A = A')
  | lf_binary Al Ar, lf_binary Al' Ar' =>
    bool_decide (Al = Al') && bool_decide (Ar = Ar')
  | _, _ => false
  end.

Lemma check_lf_clause_eq_spec {Σ N} `{!EqDecision Σ} `{!EqDecision N} (α β : lf_clause Σ N) :
  check_lf_clause_eq α β = true ↔ α = β.
Proof.
  destruct α; destruct β => //=.
  all: try rewrite !andb_true_iff.
  all: rewrite !bool_decide_eq_true.
  all: naive_solver.
Qed.

Global Instance lf_clause_eq_dec Σ N `{!EqDecision Σ} `{!EqDecision N} : EqDecision (lf_clause Σ N).
Proof.
  intros α β.
  have ? : check_lf_clause_eq α β = true ↔ α = β by apply check_lf_clause_eq_spec.
  destruct (check_lf_clause_eq α β); [left | right]; naive_solver.
Qed.

(** Layout constraints: a predicate over sentence(s) that is true when the sentence(s) is empty. *)
Definition unary_predicate (Σ : Type) : Type := {p : sentence Σ → bool & p [] = true}.
Definition app₁ {Σ : Type} (φ : unary_predicate Σ) := projT1 φ.

Definition binary_predicate (Σ : Type) : Type :=
  {p : sentence Σ → sentence Σ → bool & ∀ w1 w2, w1 = [] ∨ w2 = [] → p w1 w2 = true}.
Definition app₂ {Σ : Type} (φ : binary_predicate Σ) := projT1 φ.

(** Layout-sensitive binary normal form (LS2NF), where [Σ] is a finite set of terminals (or tokens),
    and [N] is a finite set of nonterminals.
    
    In our Coq representation:
    - [start] gives the start symbol
    - [lf_clauses] is a mapping from lhs (i.e., nonterminals) to rhs (layout free clause), which 
      indeed contains all layout-free version of production rules
    - [lf_clauses_no_dup] requires that [lf_clauses A] is a set (thus has no duplicated elements)
    - [unary_clause_predicate] and [binary_clause_predicate] attach the layout constraints to the
      production rules, say if #$A \to B^\varphi$# is a production rule, we let
      [lf_unary B ∈ lf_clauses A] and [unary_clause_predicate A B = φ]. Thanks to the nature of
      mappings, we obtain the following properties for free:
      (1) rules [A ↦ unary B φ] and [A ↦ unary B φ'] for [φ ≠ φ'] cannot appear simultaneously; and
      (2) rules [A ↦ binary B1 B2 φ] and [A ↦ binary B1 B2 φ'] for [φ ≠ φ'] cannot appear
          simultaneously
    *)
Record grammar (Σ N : Type) := {
  start : N;
  lf_clauses : N → list (lf_clause Σ N);
  lf_clauses_no_dup : ∀ A, NoDup (lf_clauses A);
  unary_clause_predicate : N → N → unary_predicate Σ;
  binary_clause_predicate : N → N → N → binary_predicate Σ;
}.

Arguments lf_clauses {_} {_}.
Arguments lf_clauses_no_dup {_} {_}.
Arguments unary_clause_predicate {_} {_}.
Arguments binary_clause_predicate {_} {_}.

(** Layout-sensitive clauses: they are what we defined in Definition 3.1. *)
Inductive clause (Σ N : Type) : Type :=
  | ε                                             (* empty clause *)
  | atom (token : Σ)                              (* atomic clause *)
  | unary (A : N) (φ : unary_predicate Σ)         (* unary clause #$A^φ$# *)
  | binary (Al Ar : N) (φ : binary_predicate Σ)   (* binary clause #$Al φ Ar$# *)
  .

Arguments ε {_} {_}.
Arguments atom {_} {_}.
Arguments unary {_} {_}.
Arguments binary {_} {_}.

Definition clauses {Σ N : Type} (G : grammar Σ N) (A : N) : list (clause Σ N) :=
  (λ α, match α with
  | lf_ε => ε
  | lf_atom a => atom a
  | lf_unary B => unary B (unary_clause_predicate G A B)
  | lf_binary Bl Br => binary Bl Br (binary_clause_predicate G A Bl Br)
  end) <$> lf_clauses G A.

(** Production rule. *)
Inductive production (Σ N : Type) : Type :=
  mk_production (lhs : N) (rhs : clause Σ N).
Arguments mk_production {_} {_}.
Notation "A ↦ α" := (mk_production A α) (at level 40) : grammar_scope.

Global Instance production_elem_of_grammar Σ N : ElemOf (production Σ N) (grammar Σ N) := λ p G,
  match p with
  | mk_production A α => α ∈ clauses G A
  end.
(** Once defined this instance for the type class [ElemOf] (provided by stdpp), one could use a more
    familiar notation [A ↦ α ∈ G] to indicate that #$A \to \alpha$# is a production rule. *)

Ltac invert H := inversion H; subst; clear H.

Section clauses.
  Context {Σ N : Type}.
  Context (G : grammar Σ N).

  Lemma elem_of_clauses A α :
    A ↦ α ∈ G → match α with
    | ε => lf_ε ∈ lf_clauses G A
    | atom a => lf_atom a ∈ lf_clauses G A
    | unary B φ => lf_unary B ∈ lf_clauses G A ∧
        φ = unary_clause_predicate G A B
    | binary Bl Br φ => lf_binary Bl Br ∈ lf_clauses G A ∧
        φ = binary_clause_predicate G A Bl Br
    end.
  Proof.
    unfold elem_of, production_elem_of_grammar.
    rewrite elem_of_list_fmap. intros [? [Heq ?]]. destruct α.
    all: case_match => //.
    all: by invert Heq.
  Qed.

  Lemma unary_clause_predicate_unique A B φ φ' :
    A ↦ unary B φ ∈ G →
    A ↦ unary B φ' ∈ G →
    φ = φ'.
  Proof.
    intros Hφ Hφ'. apply elem_of_clauses in Hφ, Hφ'.
    naive_solver.
  Qed.

  Lemma binary_clause_predicate_unique A Bl Br φ φ' :
    A ↦ binary Bl Br φ ∈ G →
    A ↦ binary Bl Br φ' ∈ G →
    φ = φ'.
  Proof.
    intros Hφ Hφ'. apply elem_of_clauses in Hφ, Hφ'.
    naive_solver.
  Qed.
End clauses.

(** * Parsing *)

Section parsing.
  Context {Σ N : Type}.

  (** Definition of parse trees: they correspond to the four constructors defined in paper.
      [r] is the root node. *)
  Inductive tree : Type :=
    | ε_tree (r : N)                          (* empty tree *)
    | token_tree (r : N) (pt : pos_token Σ)   (* leaf tree *)
    | unary_tree (r : N) (t : tree)           (* unary tree *)
    | binary_tree (r : N) (tl tr : tree)      (* binary tree *)
    .

  (** Root node (a nonterminal) of a tree. *)
  Definition root t : N :=
    match t with
    | ε_tree R => R
    | token_tree R _ => R
    | unary_tree R _ => R
    | binary_tree R _ _ => R
    end.

  (** The sentence that a tree represents. *)
  Fixpoint word t : sentence Σ :=
    match t with
    | ε_tree _ => []
    | token_tree _ tk => [tk]
    | unary_tree _ t' => word t'
    | binary_tree _ t1 t2 => word t1 ++ word t2
    end.

  (** Equality of symbols (for both terminals and nonterminals) is obviously decidable. *)
  Context `{!EqDecision Σ} `{!EqDecision N}.

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

  Context (G : grammar Σ N).

  (** A parse tree is said _valid_ if it follows the production rules and fulfills the
      layout constraints. *)
  Inductive tree_valid : tree → Prop :=
    | valid_ε A :
      A ↦ ε ∈ G →
      tree_valid (ε_tree A)
    | valid_token A a p :
      A ↦ atom a ∈ G →
      tree_valid (token_tree A (a @ p))
    | valid_unary A t' φ :
      A ↦ unary (root t') φ ∈ G →
      tree_valid t' →
      app₁ φ (word t') = true →
      tree_valid (unary_tree A t')
    | valid_binary A t1 t2 φ :
      A ↦ binary (root t1) (root t2) φ ∈ G →
      tree_valid t1 →
      tree_valid t2 →
      app₂ φ (word t1) (word t2) = true →
      tree_valid (binary_tree A t1 t2)
    .

  (** Definition of _witness_. *)
  Definition tree_witness t A w := root t = A ∧ word t = w ∧ tree_valid t.

  (** Definition of "[A] derives [w]" in a declarative fashion. *)
  Definition derive A w : Prop := ∃ t, tree_witness t A w.

End parsing.
Notation "✓{ G } t" := (tree_valid G t) (at level 40, format "'✓{' G '}'  t") : grammar_scope.
Notation "t ▷ A ={ G }=> w" := (tree_witness G t A w) (at level 40) : grammar_scope.
Notation "G ⊨ A => w" := (derive G A w) (at level 65) : grammar_scope.
