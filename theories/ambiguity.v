From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From ambig Require Import grammar.

(* standard notion of ambiguity *)

Definition sentence_ambiguous {Σ N : Type} (G : grammar Σ N) (A : N) (w : sentence Σ) : Prop :=
  ∃ t1 t2 : tree Σ N,
    (t1 ▷ A ={G}=> w) ∧ (t2 ▷ A ={G}=> w) ∧ t1 ≠ t2.

Definition ambiguous {Σ N : Type} (G : grammar Σ N) :=
  ∃ w, sentence_ambiguous G (start G) w.

(* similarity *)

(* assume input trees have same root and word *)

Definition similar {Σ N : Type} (t1 t2 : tree Σ N) : Prop :=
  match t1, t2 with
  | ε_tree _, ε_tree _ => True
  | token_tree R1 tk1, token_tree R2 tk2 => tk1 = tk2
  | unary_tree R1 t1, unary_tree R2 t2 => root t1 = root t2
  | binary_tree R1 tA1 tB1, binary_tree R2 tA2 tB2 =>
    root tA1 = root tA2 ∧ root tB1 = root tB2 ∧ sentence_of tA1 = sentence_of tA2
  | _, _ => False
  end.

Lemma similar_refl Σ N :
  Reflexive (@similar Σ N).
Proof.
  move => t.
  destruct t => //=.
Qed.

(* reachable *)

Inductive reachable {Σ N : Type} (G : grammar Σ N) : N → sentence Σ (* TODO: necessary? *) → N → sentence Σ → Prop :=
  | reachable_refl S w :
    reachable G S w S w
  | reachable_unary A B w φ H h :
    G ⊢ A ↦ unary B φ →
    reachable G B w H h →
    (w ≠ [] → φ w) →
    reachable G A w H h
  | reachable_left A Bl w1 Br w2 φ H h :
    G ⊢ A ↦ binary Bl Br φ →
    reachable G Bl w1 H h →
    G ⊨ Br ⇒ w2 →
    (w1 ≠ [] → w2 ≠ [] → φ w1 w2) →
    reachable G A (w1 ++ w2) H h
  | reachable_right A Bl w1 Br w2 φ H h :
    G ⊢ A ↦ binary Bl Br φ →
    reachable G Br w2 H h →
    G ⊨ Bl ⇒ w1 →
    (w1 ≠ [] → w2 ≠ [] → φ w1 w2) →
    reachable G A (w1 ++ w2) H h
  .

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
  induction 1; first done.
  all: inversion 1; subst.
  all: try econstructor; eauto.
Qed.

Lemma subtree_reachable {Σ N : Type} (G : grammar Σ N) t t' :
  subtree t' t →
  ✓{G} t →
  reachable G (root t) (sentence_of t) (root t') (sentence_of t').
Proof.
  induction 1; first by constructor.
  all: inversion 1; subst => /=.
  - eapply reachable_unary; eauto.
  - eapply reachable_left; eauto. by eexists.
  - eapply reachable_right; eauto. by eexists.
Qed.

(* sketch *)

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

Inductive sketch_valid {Σ N : Type} (G : grammar Σ N) : sketch Σ N → Prop :=
  | sketch_valid_hole H h :
    sketch_valid G (hole H h)
  | sketch_valid_unary A s' φ :
    G ⊢ A ↦ unary (sketch_root s') φ →
    sketch_valid G s' →
    (let w := sketch_sentence s' in w ≠ [] → φ w) →
    sketch_valid G (unary_sketch A s')
  | sketch_valid_left A s' t' φ :
    G ⊢ A ↦ binary (sketch_root s') (root t') φ →
    sketch_valid G s' →
    valid G t' →
    (let w1 := sketch_sentence s' in
     let w2 := sentence_of t' in w1 ≠ [] → w2 ≠ [] → φ w1 w2) →
    sketch_valid G (left_sketch A s' t')
  | sketch_valid_right A s' t' φ :
    G ⊢ A ↦ binary (root t') (sketch_root s') φ →
    sketch_valid G s' →
    valid G t' →
    (let w1 := sentence_of t' in
      let w2 := sketch_sentence s' in w1 ≠ [] → w2 ≠ [] → φ w1 w2) →
    sketch_valid G (right_sketch A t' s')
  .

Notation "✓ₛ{ G } t" := (sketch_valid G t) (at level 40, format "'✓ₛ{' G '}'  t").

Definition sketch_witness {Σ N : Type} (G : grammar Σ N) (s : sketch Σ N) (A : N) (w : sentence Σ) :=
  sketch_root s = A ∧ sketch_sentence s = w ∧ ✓ₛ{G} s.

Notation "s ▷ₛ A ={ G }=> w" := (sketch_witness G s A w) (at level 40, format "s  '▷ₛ'  A  '={' G '}=>'  w").

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
  hole_sig s = (root t, sentence_of t) →
  root (instantiate s t) = sketch_root s.
Proof.
  destruct s => /=.
  all: by inversion 1.
Qed.

Lemma instantiate_word {Σ N} (s : sketch Σ N) t :
  hole_sig s = (root t, sentence_of t) →
  sentence_of (instantiate s t) = sketch_sentence s.
Proof.
  induction s => /=.
  all: inversion 1; subst => //=.
  all: by rewrite IHs.
Qed.

Lemma instantiate_witness {Σ N : Type} G (s : sketch Σ N) t :
  hole_sig s = (root t, sentence_of t) →
  ✓{G} t →
  ✓ₛ{G} s →
  ✓{G} instantiate s t.
Proof.
  induction s => /=.
  all: inversion 1; subst => Ht Hs /=.
  all: inversion Hs; subst; clear Hs => //=.
  all: econstructor; rewrite ?instantiate_root ?instantiate_word;
    eauto.
Qed.

Lemma reachable_sketch_intro {Σ N : Type} (G : grammar Σ N) S w H h :
  reachable G S w H h →
  ∃ (s : sketch Σ N), hole_sig s = (H, h) ∧ s ▷ₛ S ={G}=> w.
Proof.
  induction 1.
  - exists (hole S w).
    split; first done.
    repeat split. constructor.
  - destruct IHreachable as [s' [? [? [? ?]]]].
    exists (unary_sketch A s') => /=.
    split; first done.
    repeat split; first naive_solver.
    econstructor. subst. all: naive_solver.
  - destruct IHreachable as [sl [? [? [? ?]]]].
    destruct H2 as [tr [? [? ?]]].
    exists (left_sketch A sl tr) => /=.
    split; first done.
    repeat split; first naive_solver.
    econstructor. subst. all: naive_solver.
  - destruct IHreachable as [sr [? [? [? ?]]]].
    destruct H2 as [tl [? [? ?]]].
    exists (right_sketch A tl sr) => /=.
    split; first done.
    repeat split; first naive_solver.
    econstructor. subst. all: naive_solver.
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
  (G : grammar Σ N) A w :
  sentence_ambiguous G A w ↔ ∃ H h, reachable G A w H h ∧
    ∃ t1 t2, t1 ▷ H ={G}=> h ∧ t2 ▷ H ={G}=> h ∧ ¬ (similar t1 t2).
Proof.
  split.
  - move => [t1 [t2 [[Hr1 [Hw1 ?]] [[? [? ?]] ?]]]].
    have [[t1' t2'] Hdiff] : is_Some (diff t1 t2).
    { apply not_eq_None_Some. intros Hcontra. apply diff_None in Hcontra => //.
      all: congruence. }
    have [Hsub1 Hsub2] := (diff_result_subtree _ _ _ _ Hdiff).
    exists (root t1'), (sentence_of t1').
    split; first by rewrite -Hr1 -Hw1; apply subtree_reachable.
    exists t1', t2'.
    have [? ?] : root t1' = root t2' ∧ sentence_of t1' = sentence_of t2'.
    { eapply diff_Some_inv; last eauto. all: congruence. }
    repeat split => //.
    1,2: eapply subtree_valid; eauto.
    eapply diff_result_not_similar; eauto.
  - move => [H [h [Hr [t1 [t2 [Ht1 [Ht2 Hnot]]]]]]].
    destruct Ht1 as [? [? ?]].
    destruct Ht2 as [? [? ?]].
    have [s [w' [? [? ?]]]] := (reachable_sketch_intro _ _ _ _ _ Hr).
    exists (instantiate s t1), (instantiate s t2).
    repeat split => //=.
    all: try by rewrite instantiate_root; congruence.
    all: try by rewrite instantiate_word; congruence.
    all: try by eapply instantiate_witness; congruence.
    move => ?. apply Hnot.
    have -> : t1 = t2 by eapply inj; eauto; apply instantiate_inj.
    apply similar_refl.
Qed.
