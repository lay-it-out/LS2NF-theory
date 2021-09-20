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

Fixpoint sketch_sentence {Σ N : Type} (s : sketch Σ N) : sentence Σ :=
  match s with
  | hole _ h => h
  | unary_sketch _ s' => sketch_sentence s'
  | left_sketch _ s' t' => sketch_sentence s' ++ sentence_of t'
  | right_sketch _ t' s' => sentence_of t' ++ sketch_sentence s'
  end.

Fixpoint hole_sig {Σ N : Type} (s : sketch Σ N) : N * sentence Σ :=
  match s with
  | hole H h => (H, h)
  | unary_sketch _ s' => hole_sig s'
  | left_sketch _ s' _ => hole_sig s'
  | right_sketch _ _ s' => hole_sig s'
  end.

Reserved Notation "s ▷ₛ A ={ G }=> w" (at level 40, format "s  '▷ₛ'  A  '={' G '}=>'  w").

Inductive sketch_witness {Σ N : Type} (G : grammar Σ N) : sketch Σ N → N → sentence Σ → Prop :=
  | sketch_valid_hole H h :
    hole H h ▷ₛ H ={G}=> h
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

Lemma instantiate_witness {Σ N : Type} G H h (s : sketch Σ N) t A w :
  hole_sig s = (H, h) →
  t ▷ H ={G}=> h →
  s ▷ₛ A ={G}=> w →
  instantiate s t ▷ A ={G}=> w.
Proof.
  move => Hsig Ht.
  move : A w.
  induction s => A w Hs /=.
  all: inversion Hs; subst; clear Hs => //.
  all: inversion Hsig; subst => //.
  all: econstructor => //; by apply IHs.
Qed.

Fixpoint sketch_subst {Σ N : Type} (s : sketch Σ N) (t : sketch Σ N) : sketch Σ N :=
  match s with
  | hole _ _ => t
  | unary_sketch R s' => unary_sketch R (sketch_subst s' t)
  | left_sketch R s' t' => left_sketch R (sketch_subst s' t) t'
  | right_sketch R t' s' => right_sketch R t' (sketch_subst s' t)
  end.

Lemma subst_witness {Σ N : Type} G (s : sketch Σ N) (t : sketch Σ N) H h A w :
  hole_sig s = (H, h) →
  t ▷ₛ H ={G}=> h →
  s ▷ₛ A ={G}=> w →
  sketch_subst s t ▷ₛ A ={G}=> w.
Proof.
  move => Hsig Ht.
  move : A w.
  induction s => A w Hs /=.
  all: inversion Hs; subst; clear Hs => //.
  all: inversion Hsig; subst => //.
  all: econstructor => //; by apply IHs.
Qed.

Lemma subst_hole_sig {Σ N : Type} (s : sketch Σ N) (t : sketch Σ N) :
  hole_sig (sketch_subst s t) = hole_sig t.
Proof.
  by induction s.
Qed.

Definition similar {Σ N : Type} (t1 t2 : tree Σ N) : Prop :=
  match t1, t2 with
  | ε_tree R1, ε_tree R2 => R1 = R2
  | token_tree R1 tk1, token_tree R2 tk2 =>
    R1 = R2 ∧ tk1 = tk2
  | unary_tree R1 t1, unary_tree R2 t2 =>
    R1 = R2 ∧ root t1 = root t2
  | binary_tree R1 tA1 tB1, binary_tree R2 tA2 tB2 =>
    R1 = R2 ∧ root tA1 = root tA2 ∧ root tB1 = root tB2 ∧ sentence_of tA1 = sentence_of tA2
  | _, _ => False
  end.

Lemma similar_refl Σ N :
  Reflexive (@similar Σ N).
Proof.
  move => t.
  destruct t => //=.
Qed.

(* diff two trees with same root and sentence *)
Fixpoint diff {Σ N : Type} `{EqDecision N} `{EqDecision (token Σ)}
  (t1 t2 : tree Σ N) : option (tree Σ N * tree Σ N) :=
  match t1, t2 with
  | ε_tree _, ε_tree _ => None
  | token_tree _ _, token_tree _ _ =>
    (* tokens must be eq, so no diff *)
    None
  | unary_tree _ t1', unary_tree _ t2' =>
    (* sentences must be eq, so just compare root *)
    if bool_decide (root t1' = root t2')
    then diff t1' t2'
    else Some (t1, t2)
  | binary_tree _ tl1 tr1, binary_tree _ tl2 tr2 =>
    if bool_decide (root tl1 = root tl2 ∧ root tr1 = root tr2 ∧ sentence_of tl1 = sentence_of tl2)
    then
      match diff tl1 tl2 with
      | Some p => Some p
      | None => diff tr1 tr2
      end
    else Some (t1, t2)
  | _, _ => Some (t1, t2)
  end.

Lemma diff_None {Σ N : Type} `{EqDecision N} `{EqDecision (token Σ)} (t1 t2 : tree Σ N) :
  root t1 = root t2 →
  sentence_of t1 = sentence_of t2 →
  t1 = t2 ↔ diff t1 t2 = None.
Proof.
  intros. split.
  - intros <-.
    induction t1 => //=.
    + case_bool_decide => //. by apply IHt1.
    + case_bool_decide => //=.
      * rewrite IHt1_1 => //. rewrite IHt1_2 => //.
      * exfalso. naive_solver.
  - generalize dependent t2.
    induction t1 => t2.
    all: destruct t2 => Hr Hw Hdiff //=.
    1,2: naive_solver.
    + simpl in Hr; subst.
      simpl in Hdiff. case_bool_decide => //.
      erewrite IHt1; eauto.
    + simpl in Hr; subst.
      simpl in Hdiff. case_bool_decide => //.
      case_match => //.
      erewrite (IHt1_1 t2_1).
      erewrite (IHt1_2 t2_2).
      all: eauto; naive_solver.
Qed.

Lemma diff_Some_inv {Σ N : Type} `{EqDecision N} `{EqDecision (token Σ)} (t1 t2 t1' t2' : tree Σ N) :
  root t1 = root t2 →
  sentence_of t1 = sentence_of t2 →
  diff t1 t2 = Some (t1', t2') →
  root t1' = root t2' ∧ sentence_of t1' = sentence_of t2'.
Proof.
  generalize dependent t2.
  induction t1 => t2.
  all: destruct t2 => //= -> Hw Hdiff.
  all: inversion Hdiff; subst; clear Hdiff.
  all: try naive_solver.
  - case_bool_decide.
    * eapply IHt1; eauto.
    * inversion H0; subst; clear H0. done.
  - case_bool_decide; first case_match.
    * naive_solver.
    * destruct H as [? [? ?]]. eapply (IHt1_2 t2_2); eauto.
      rewrite H2 in Hw. by eapply app_inv_head_iff.
    * naive_solver.
Qed.

Lemma diff_result_not_similar {Σ N : Type} `{EqDecision N} `{EqDecision (token Σ)} (t1 t2 t1' t2' : tree Σ N) :
  diff t1 t2 = Some (t1', t2') → ¬ (similar t1' t2').
Proof.
  generalize dependent t2.
  induction t1 => t2.
  all: destruct t2 => //= Hdiff.
  all: inversion Hdiff; subst; clear Hdiff.
  all: try naive_solver.
  - case_bool_decide; naive_solver.
  - case_bool_decide; first case_match; naive_solver.
Qed.

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

Lemma subtree_witness {Σ N : Type} (G : grammar Σ N) t t' A w :
  subtree t' t →
  t ▷ A ={ G }=> w →
  t' ▷ (root t') ={ G }=> (sentence_of t').
Admitted.

Lemma subtree_sketch_intro {Σ N : Type} (G : grammar Σ N) t t' :
  t ▷ (root t) ={ G }=> (sentence_of t) →
  subtree t' t →
  ∃ s, hole_sig s = (root t', sentence_of t') ∧ s ▷ₛ (root t) ={ G }=> (sentence_of t).
Proof.
  intros Ht.
  induction 1.
  - exists (hole (root t) (sentence_of t)).
    split; first done.
    constructor.
  - edestruct IHsubtree as [s [? ?]].
    { eapply subtree_witness; eauto. constructor. constructor. }
    exists (unary_sketch R s).
    split; first done.
    inversion Ht; subst; clear Ht => /=.
    econstructor; eauto.
    have <- : root t' = B by inversion H5. done.
  - edestruct IHsubtree as [s [? ?]].
    { eapply subtree_witness; eauto. constructor. constructor. }
    exists (left_sketch R s tr).
    split; first done.
    inversion Ht; subst; clear Ht => /=.
    econstructor; eauto.
    have <- : root tl = B1 by inversion H8. done.
    have -> : sentence_of tr = w2 by admit. done.
    admit.
  - edestruct IHsubtree as [s [? ?]].
    { eapply subtree_witness; eauto. apply subtree_right. constructor. }
    exists (right_sketch R tl s).
    split; first done.
    inversion Ht; subst; clear Ht => /=.
    econstructor; eauto.
    admit. admit. admit.
Admitted.

Lemma diff_result_subtree {Σ N : Type} `{EqDecision N} `{EqDecision (token Σ)} (t1 t2 t1' t2' : tree Σ N) :
  diff t1 t2 = Some (t1', t2') → subtree t1' t1 ∧ subtree t2' t2.
Proof.
  generalize dependent t2.
  induction t1 => t2.
  all: destruct t2 => //= Hdiff.
  all: inversion Hdiff; subst; clear Hdiff.
  all: try by split; constructor.
  - case_bool_decide.
    * edestruct IHt1; eauto. split; by constructor.
    * inversion H0; subst. split; by constructor.
  - case_bool_decide; first case_match.
    * edestruct (IHt1_1 t2_1); eauto; try congruence. split; by constructor.
    * edestruct (IHt1_2 t2_2); eauto. split; by constructor.
    * inversion H0; subst. split; by constructor.
Qed.

Lemma sentence_ambiguous_iff {Σ N : Type} `{EqDecision N} `{EqDecision (token Σ)}
  (G : grammar Σ N) w :
  sentence_ambiguous G w ↔ ∃ H h (s : sketch Σ N),
    s ▷ₛ (start G) ={G}=> w ∧ hole_sig s = (H, h) ∧ ∃ t1 t2, ¬ (similar t1 t2) ∧
      t1 ▷ H ={G}=> h ∧ t2 ▷ H ={G}=> h.
Proof.
  split.
  - move => [t1 [t2 [Ht1 [Ht2 ?]]]].
    have ? : root t1 = start G by inversion Ht1.
    have ? : root t2 = start G by inversion Ht2.
    have ? : sentence_of t1 = w by admit.
    have ? : sentence_of t2 = w by admit.
    have [[t1' t2'] Hdiff] : is_Some (diff t1 t2).
    { apply not_eq_None_Some. intros Hcontra. apply diff_None in Hcontra => //.
      all: congruence. }
    have [Hsub1 Hsub2] := (diff_result_subtree _ _ _ _ Hdiff).
    have Ht1' : t1 ▷ root t1 ={ G }=> sentence_of t1 by congruence.
    have Ht2' : t2 ▷ root t2 ={ G }=> sentence_of t2 by congruence.
    destruct (subtree_sketch_intro G _ _ Ht1' Hsub1) as [s [? ?]].
    exists (root t1'), (sentence_of t1'), s.
    split; first congruence.
    split; first done.
    exists t1', t2'. split; first by eapply diff_result_not_similar.
    split; first by eapply subtree_witness; eauto.
    have [-> ->] : root t1' = root t2' ∧ sentence_of t1' = sentence_of t2'.
    { eapply diff_Some_inv; last eauto. all: congruence. }
    eapply subtree_witness; eauto.
  - move => [H [h [s [Hs [Hsig [t1 [t2 [Hne [Ht1 Ht2]]]]]]]]].
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
  ∃ (s : sketch Σ N) w, hole_sig s = (H, h) ∧ s ▷ₛ (start G) ={G}=> w.
Proof.
  induction 1; subst.
  - exists (hole (start G) w), w.
    split; first done. constructor.
  - destruct IHreachable as [s' [w' [? ?]]].
    exists (sketch_subst s' (unary_sketch A (hole B w))), w' => /=.
    split; first by rewrite subst_hole_sig.
    eapply subst_witness => //.
    econstructor => //. constructor.
  - destruct IHreachable as [sA [wA [? ?]]].
    destruct H1 as [tB' ?].
    exists (sketch_subst sA (left_sketch A (hole B w) tB')), wA => /=.
    split; first by rewrite subst_hole_sig.
    eapply subst_witness => //.
    econstructor => //. constructor.
  - destruct IHreachable as [sA [wA [? ?]]].
    destruct H1 as [tB' ?].
    exists (sketch_subst sA (right_sketch A tB' (hole B w))), wA => /=.
    split; first by rewrite subst_hole_sig.
    eapply subst_witness => //.
    econstructor => //. constructor.
Qed.
