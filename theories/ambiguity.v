From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From ambig Require Import grammar.

(* standard notion of ambiguity *)

Definition sentence_ambiguous {Σ N : Type} (G : grammar Σ N) (w : sentence Σ) : Prop :=
  ∃ t1 t2 : tree Σ N,
    (t1 ▷ (start G) ={G}=> w) ∧ (t2 ▷ (start G) ={G}=> w) ∧ t1 ≠ t2.

Definition ambiguous {Σ N : Type} (G : grammar Σ N) :=
  ∃ w, sentence_ambiguous G w.

(* bounded ambiguity *)

Inductive sketch (Σ N : Type) (H : N) (h : sentence Σ) : Type :=
  | hole : sketch Σ N H h
  | unary_sketch : N → sketch Σ N H h → sketch Σ N H h
  | left_sketch : N → sketch Σ N H h → tree Σ N → sketch Σ N H h
  | right_sketch : N → tree Σ N → sketch Σ N H h → sketch Σ N H h
  .

Arguments hole {_} {_} {_} {_}.
Arguments unary_sketch {_} {_} {_} {_}.
Arguments left_sketch {_} {_} {_} {_}.
Arguments right_sketch {_} {_} {_} {_}.

Definition sketch_root {Σ N : Type} {H h} (s : sketch Σ N H h) : N :=
  match s with
  | hole => H
  | unary_sketch R _ => R
  | left_sketch R _ _ => R
  | right_sketch R _ _ => R
  end.

Fixpoint sketch_sentence {Σ N : Type} {H h} (s : sketch Σ N H h) : sentence Σ :=
  match s with
  | hole => h
  | unary_sketch _ s' => sketch_sentence s'
  | left_sketch _ s' t' => sketch_sentence s' ++ sentence_of t'
  | right_sketch _ t' s' => sentence_of t' ++ sketch_sentence s'
  end.

Reserved Notation "s ▷ₛ A ={ G }=> w" (at level 40, format "s  '▷ₛ'  A  '={' G '}=>'  w").

Inductive sketch_witness {Σ N : Type} (G : grammar Σ N) {H h} : sketch Σ N H h → N → sentence Σ → Prop :=
  | sketch_valid_hole :
    hole ▷ₛ H ={G}=> h
  | sketch_valid_unary A B φ s w :
    G ⊢ A ↦ unary B φ →
    s ▷ₛ B ={G}=> w →
    (w ≠ [] → φ w) →
    unary_sketch A s ▷ₛ A ={G}=> w
  | sketch_valid_left A B1 B2 φ s w1 t w2 :
    G ⊢ A ↦ binary B1 B2 φ →
    s ▷ₛ B1 ={G}=> w1 →
    t ▷ B2 ={G}=> w2 →
    (w1 ≠ [] → w2 ≠ [] → φ w1 w2) →
    left_sketch A s t ▷ₛ A ={G}=> (w1 ++ w2)
  | sketch_valid_right A B1 B2 φ t w1 s w2 :
    G ⊢ A ↦ binary B1 B2 φ →
    t ▷ B1 ={G}=> w1 →
    s ▷ₛ B2 ={G}=> w2 →
    (w1 ≠ [] → w2 ≠ [] → φ w1 w2) →
    right_sketch A t s ▷ₛ A ={G}=> (w1 ++ w2)
  where "s ▷ₛ A ={ G }=> w" := (sketch_witness G s A w).

Fixpoint instantiate {Σ N : Type} {H h} (s : sketch Σ N H h) (t : tree Σ N) :=
  match s with
  | hole => t
  | unary_sketch R s' => unary_tree R (instantiate s' t)
  | left_sketch R s' t' => binary_tree R (instantiate s' t) t'
  | right_sketch R t' s' => binary_tree R t' (instantiate s' t)
  end.

Lemma instantiate_inj {Σ N H h} (s : sketch Σ N H h) :
  Inj eq eq (instantiate s).
Proof.
  move => t1 t2.
  induction s => /=.
  all: naive_solver.
Qed.

Lemma instantiate_witness {Σ N : Type} G {H h} (s : sketch Σ N H h) t A w :
  t ▷ H ={G}=> h →
  s ▷ₛ A ={G}=> w →
  instantiate s t ▷ A ={G}=> w.
Proof.
  move => Ht.
  move : A w.
  induction s => A w Hs /=.
  all: inversion Hs; subst; clear Hs => //.
  all: econstructor => //; by apply IHs.
Qed.

Fixpoint sketch_subst {Σ N : Type} {H h H' h'} (s : sketch Σ N H h) (t : sketch Σ N H' h') : sketch Σ N H' h' :=
  match s with
  | hole => t
  | unary_sketch R s' => unary_sketch R (sketch_subst s' t)
  | left_sketch R s' t' => left_sketch R (sketch_subst s' t) t'
  | right_sketch R t' s' => right_sketch R t' (sketch_subst s' t)
  end.

Lemma subst_witness {Σ N : Type} G {H h H' h'} (s : sketch Σ N H h) (t : sketch Σ N H' h') A w :
  t ▷ₛ H ={G}=> h →
  s ▷ₛ A ={G}=> w →
  sketch_subst s t ▷ₛ A ={G}=> w.
Proof.
  move => Ht.
  move : A w.
  induction s => A w Hs /=.
  all: inversion Hs; subst; clear Hs => //.
  all: econstructor => //; by apply IHs.
Qed.

Definition similar {Σ N : Type} (t1 t2 : tree Σ N) : Prop :=
  match t1, t2 with
  | ε_tree R1, ε_tree R2 => R1 = R2
  | token_tree R1 tk1, token_tree R2 tk2 =>
    R1 = R2 ∧ tk1 = tk2
  | unary_tree R1 t1, unary_tree R2 t2 =>
    R1 = R2 ∧ root t1 = root t2
  | binary_tree R1 tA1 tB1, binary_tree R2 tA2 tB2 =>
    R1 = R2 ∧ root tA1 = root tA2 ∧ root tB1 = root tB2
  | _, _ => False
  end.

Lemma similar_refl Σ N :
  Reflexive (@similar Σ N).
Proof.
  move => t.
  destruct t => //=.
Qed.

Lemma sentence_ambiguous_iff {Σ N : Type} (G : grammar Σ N) w :
  sentence_ambiguous G w ↔ ∃ H h (s : sketch Σ N H h),
    s ▷ₛ (start G) ={G}=> w ∧ ∃ t1 t2, ¬ (similar t1 t2) ∧
      t1 ▷ H ={G}=> h ∧ t2 ▷ H ={G}=> h.
Proof.
  split. admit.
  - move => [H [h [s [Hs [t1 [t2 [Hne [Ht1 Ht2]]]]]]]].
    eapply instantiate_witness in Ht1; eauto.
    eapply instantiate_witness in Ht2; eauto.
    exists (instantiate s t1), (instantiate s t2). repeat split => //.
    move => ?. apply Hne.
    have -> : t1 = t2 by eapply inj; eauto; apply instantiate_inj.
    apply similar_refl.
Admitted.

(* reachable *)
Inductive reachable {Σ N : Type} (G : grammar Σ N) : N → sentence Σ → Prop :=
  | reachable_start w :
    reachable G (start G) w
  | reachable_unary A B w φ :
    G ⊢ A ↦ unary B φ →
    reachable G A w →
    (w ≠ [] → φ w) →
    reachable G B w
  | reachable_left A B w B' w' φ :
    G ⊢ A ↦ binary B B' φ →
    reachable G A (w ++ w') →
    G ⊨ B' ⇒ w' →
    (w ≠ [] → w' ≠ [] → φ w w') →
    reachable G B w
  | reachable_right A B' w' B w φ :
    G ⊢ A ↦ binary B' B φ →
    reachable G A (w' ++ w) →
    G ⊨ B' ⇒ w' →
    (w' ≠ [] → w ≠ [] → φ w' w) →
    reachable G B w
  .

Lemma reachable_sketch_intro {Σ N : Type} (G : grammar Σ N) H h :
  reachable G H h →
  ∃ (s : sketch Σ N H h) w, s ▷ₛ (start G) ={G}=> w.
Proof.
  induction 1; subst.
  - exists hole, w. constructor.
  - destruct IHreachable as [s' [w' ?]].
    exists (sketch_subst s' (unary_sketch A hole)), w' => /=.
    apply subst_witness => //.
    econstructor => //. constructor.
  - destruct IHreachable as [sA [wA ?]].
    destruct H1 as [tB' ?].
    exists (sketch_subst sA (left_sketch A hole tB')), wA => /=.
    apply subst_witness => //.
    econstructor => //. constructor.
  - destruct IHreachable as [sA [wA ?]].
    destruct H1 as [tB' ?].
    exists (sketch_subst sA (right_sketch A tB' hole)), wA => /=.
    apply subst_witness => //.
    econstructor => //. constructor.
Qed.
