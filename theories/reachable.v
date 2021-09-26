From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From ambig Require Import grammar.

(* reachability with layout constraints/predicates *)

Inductive reachable {Σ N : Type} (G : grammar Σ N) : N → sentence Σ (* TODO: necessary? *) → N → sentence Σ → Prop :=
  | reachable_refl S w S' w' :
    S = S' →
    w = w' →
    reachable G S w S' w'
  | reachable_unary A B w φ H h :
    A ↦ unary B φ ∈ G →
    reachable G B w H h →
    φ w →
    reachable G A w H h
  | reachable_left A Bl w1 Br w2 φ H h :
    A ↦ binary Bl Br φ ∈ G →
    reachable G Bl w1 H h →
    G ⊨ Br ⇒ w2 →
    φ w1 w2 →
    reachable G A (w1 ++ w2) H h
  | reachable_right A Bl w1 Br w2 φ H h :
    A ↦ binary Bl Br φ ∈ G →
    reachable G Br w2 H h →
    G ⊨ Bl ⇒ w1 →
    φ w1 w2 →
    reachable G A (w1 ++ w2) H h
  .

(* tree-representation of reachability *)

Inductive sketch (Σ N : Type) : Type :=
  | hole : N → sentence Σ → sketch Σ N
  | unary_sketch : N → sketch Σ N → sketch Σ N
  | left_sketch : N → sketch Σ N → tree Σ N → sketch Σ N
  | right_sketch : N → tree Σ N → sketch Σ N → sketch Σ N
  .

Arguments hole {_} {_}.
Arguments unary_sketch {_} {_}.
Arguments left_sketch {_} {_}.
Arguments right_sketch {_} {_}.

Definition sketch_root {Σ N : Type} (s : sketch Σ N) : N :=
  match s with
  | hole H _ => H
  | unary_sketch R _ => R
  | left_sketch R _ _ => R
  | right_sketch R _ _ => R
  end.

Fixpoint sketch_word {Σ N : Type} (s : sketch Σ N) : sentence Σ :=
  match s with
  | hole _ h => h
  | unary_sketch _ s' => sketch_word s'
  | left_sketch _ s' t' => sketch_word s' ++ word t'
  | right_sketch _ t' s' => word t' ++ sketch_word s'
  end.

Fixpoint sketch_valid {Σ N : Type} (G : grammar Σ N) (s : sketch Σ N) : bool :=
  match s with
  | hole _ _ => true
  | unary_sketch A s' =>
    match unary_productions G A (sketch_root s') with
    | Some φ => sketch_valid G s' && φ (sketch_word s')
    | None => false
    end
  | left_sketch A s' t' =>
    match binary_productions G A (sketch_root s') (root t') with
    | Some φ => sketch_valid G s' && ✓{G} t' && φ (sketch_word s') (word t')
    | None => false
    end
  | right_sketch A t' s' =>
    match binary_productions G A (root t') (sketch_root s') with
    | Some φ => ✓{G} t' && sketch_valid G s' && φ (word t') (sketch_word s')
    | None => false
    end
  end.

Global Instance ParseTree_sketch Σ N : ParseTree Σ N sketch := {|
  root := sketch_root;
  word := sketch_word;
  valid := sketch_valid;
|}.

Lemma valid_unary_sketch {Σ N : Type} (G : grammar Σ N) A φ s :
  A ↦ unary (root s) φ ∈ G →
  φ (word s) →
  ✓{G} s →
  ✓{G} unary_sketch A s.
Proof.
  intros HA ? ?. simpl.
  rewrite HA. naive_solver.
Qed.

Lemma valid_left_sketch {Σ N : Type} (G : grammar Σ N) A φ s t :
  A ↦ binary (root s) (root t) φ ∈ G →
  φ (word s) (word t) →
  ✓{G} s →
  ✓{G} t →
  ✓{G} left_sketch A s t.
Proof.
  intros HA ? ? ?. simpl.
  rewrite HA. naive_solver.
Qed.

Lemma valid_right_sketch {Σ N : Type} (G : grammar Σ N) A φ t s :
  A ↦ binary (root t) (root s) φ ∈ G →
  φ (word t) (word s) →
  ✓{G} t →
  ✓{G} s →
  ✓{G} right_sketch A t s.
Proof.
  intros HA ? ? ?. simpl.
  rewrite HA. naive_solver.
Qed.

Lemma valid_unary_sketch_inv {Σ N : Type} (G : grammar Σ N) A s :
  ✓{G} unary_sketch A s →
  ∃ φ, A ↦ unary (root s) φ ∈ G ∧ φ (word s) ∧ ✓{G} s.
Proof.
  simpl. case_match; naive_solver.
Qed.

Lemma valid_left_sketch_inv {Σ N : Type} (G : grammar Σ N) A s t :
  ✓{G} left_sketch A s t →
  ∃ φ, A ↦ binary (root s) (root t) φ ∈ G ∧ φ (word s) (word t) ∧ ✓{G} s ∧ ✓{G} t.
Proof.
  simpl. case_match; naive_solver.
Qed.

Lemma valid_right_sketch_inv {Σ N : Type} (G : grammar Σ N) A t s :
  ✓{G} right_sketch A t s →
  ∃ φ, A ↦ binary (root t) (root s) φ ∈ G ∧ φ (word t) (word s) ∧ ✓{G} t ∧ ✓{G} s.
Proof.
  simpl. case_match; naive_solver.
Qed.

Fixpoint sig {Σ N : Type} (s : sketch Σ N) : N * sentence Σ :=
  match s with
  | hole H h => (H, h)
  | unary_sketch _ s' => sig s'
  | left_sketch _ s' _ => sig s'
  | right_sketch _ _ s' => sig s'
  end.

Lemma reachable_sketch {Σ N : Type} (G : grammar Σ N) S w H h :
  reachable G S w H h →
  ∃ (s : sketch Σ N), sig s = (H, h) ∧ s ▷ S ={G}=> w.
Proof.
  induction 1.
  - exists (hole S w).
    split; first naive_solver.
    repeat split.
  - destruct IHreachable as [s' [? [? [? ?]]]].
    exists (unary_sketch A s') => /=.
    split; first done.
    repeat split; try naive_solver.
    eapply valid_unary_sketch; naive_solver.
  - destruct IHreachable as [sl [? [? [? ?]]]].
    destruct H2 as [tr [? [? ?]]].
    exists (left_sketch A sl tr) => /=.
    split; first done.
    repeat split; try naive_solver.
    eapply valid_left_sketch; naive_solver.
  - destruct IHreachable as [sr [? [? [? ?]]]].
    destruct H2 as [tl [? [? ?]]].
    exists (right_sketch A tl sr) => /=.
    split; first done.
    repeat split; first naive_solver.
    eapply valid_right_sketch; naive_solver.
Qed.

(* reachable and ambiguity *)

Fixpoint instantiate {Σ N : Type} (s : sketch Σ N) (t : tree Σ N) :=
  match s with
  | hole _ _ => t
  | unary_sketch R s' => unary_tree R (instantiate s' t)
  | left_sketch R s' t' => binary_tree R (instantiate s' t) t'
  | right_sketch R t' s' => binary_tree R t' (instantiate s' t)
  end.

Lemma instantiate_inj {Σ N} (s : sketch Σ N) :
  Inj eq eq (instantiate s).
Proof.
  move => t1 t2.
  induction s => /=.
  all: naive_solver.
Qed.

Lemma instantiate_root {Σ N} (s : sketch Σ N) t :
  sig s = (root t, word t) →
  tree_root (instantiate s t) = root s.
Proof.
  destruct s => /=.
  all: by inversion 1.
Qed.

Lemma instantiate_word {Σ N} (s : sketch Σ N) t :
  sig s = (root t, word t) →
  tree_word (instantiate s t) = word s.
Proof.
  induction s => /=.
  all: inversion 1 as [Hs]; subst => //=.
  all: specialize (IHs Hs); by rewrite IHs.
Qed.

Lemma instantiate_valid {Σ N : Type} G (s : sketch Σ N) t :
  sig s = (root t, word t) →
  ✓{G} s →
  ✓{G} t →
  ✓{G} instantiate s t.
Proof.
  intros Hsig Hs Ht.
  induction s.
  all: inversion Hsig; subst; clear Hsig.
  - done.
  - apply valid_unary_sketch_inv in Hs as [φ [Hp [? ?]]].
    simpl. rewrite instantiate_root ?instantiate_word ?Hp => //.
    naive_solver.
  - apply valid_left_sketch_inv in Hs as [φ [Hp [? [? ?]]]].
    simpl. rewrite instantiate_root ?instantiate_word ?Hp => //.
    naive_solver.
  - apply valid_right_sketch_inv in Hs as [φ [Hp [? [? ?]]]].
    simpl. rewrite instantiate_root ?instantiate_word ?Hp => //.
    naive_solver.
Qed.

Lemma reachable_derive_amb {Σ N} (G : grammar Σ N) A w B w' :
  reachable G A w B w' →
  derive_amb G B w' →
  derive_amb G A w.
Proof.
  intros Hr Hamb.
  apply reachable_sketch in Hr as [s [Hsig [? [? Hs]]]].
  destruct Hamb as [t1 [t2 [[? [? Ht1]] [[? [? Ht2]] Hne]]]].
  exists (instantiate s t1), (instantiate s t2).
  repeat split; simpl.
  all: try by rewrite instantiate_root; congruence.
  all: try by rewrite instantiate_word; congruence.
  all: try by apply instantiate_valid; congruence.
  intros Hcontra. apply instantiate_inj in Hcontra. contradiction.
Qed.

(* subtree *)

Inductive subtree {Σ N : Type} : tree Σ N → tree Σ N → Prop :=
  | subtree_refl t : subtree t t
  | subtree_unary R t t' : 
    subtree t t' →
    subtree t (unary_tree R t')
  | subtree_left R t tl tr :
    subtree t tl →
    subtree t (binary_tree R tl tr)
  | subtree_right R t tl tr :
    subtree t tr →
    subtree t (binary_tree R tl tr)
  .

Lemma subtree_valid {Σ N : Type} (G : grammar Σ N) t t' :
  subtree t' t →
  ✓{G} t →
  ✓{G} t'.
Proof.
  induction 1 => Ht; first done.
  1: apply valid_unary_tree_inv in Ht as [φ [? [? ?]]].
  2,3: apply valid_binary_tree_inv in Ht as [φ [? [? [? ?]]]].
  all: naive_solver.
Qed.

Lemma subtree_reachable {Σ N : Type} (G : grammar Σ N) t t' :
  subtree t' t →
  ✓{G} t →
  reachable G (root t) (word t) (root t') (word t').
Proof.
  induction 1 => Ht; first by constructor.
  1: apply valid_unary_tree_inv in Ht as [φ [? [? ?]]].
  2,3: apply valid_binary_tree_inv in Ht as [φ [? [? [? ?]]]].
  - eapply reachable_unary; eauto.
  - simpl. eapply reachable_left; eauto. by eexists.
  - simpl. eapply reachable_right; eauto. by eexists.
Qed.

(* tree inequality *)

Lemma strict_subtree_ne_unary {Σ N : Type} (t : tree Σ N) A :
  t ≠ unary_tree A t.
Proof.
  induction t; naive_solver.
Qed.

Lemma strict_subtree_ne_binary_left {Σ N : Type} (t t' : tree Σ N) A :
  t ≠ binary_tree A t t'.
Proof.
  induction t; naive_solver.
Qed.

Lemma strict_subtree_ne_binary_right {Σ N : Type} (t t' : tree Σ N) A :
  t ≠ binary_tree A t' t.
Proof.
  induction t; naive_solver.
Qed.
