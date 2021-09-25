From stdpp Require Import relations.
From Coq Require Import ssreflect.
From ambig Require Import grammar local_amb.
(* TODO: reachable in a separate file *)

(* On the graph representation of the grammar: direct edge *)
Inductive succ {Σ N : Type} (G : grammar Σ N) : relation N :=
  | succ_unary A B φ :
    G ⊢ A ↦ unary B φ →
    succ G A B
  | succ_left A B E φ :
    G ⊢ A ↦ binary B E φ →
    nullable G E = true →
    succ G A B
  | succ_right A B E φ :
    G ⊢ A ↦ binary E B φ →
    nullable G E = true →
    succ G A B
  .

(* On graph: do not have non-trivial cycles (a cycle with min length 2) *)
Definition unit {Σ N : Type} (G : grammar Σ N) : Prop :=
  ¬ ∃ A B, A ≠ B ∧ succ G A B ∧ ex_loop (succ G) B.

(* every grammar can be unitized *)

(* acyclic *)

Definition acyclic {Σ N : Type} (G : grammar Σ N) : Prop :=
  ¬ ∃ A, ex_loop (succ G) A.

Lemma acyclic_succ_flip_wf {Σ N} (G : grammar Σ N) :
  acyclic G → wf (flip (succ G)).
Admitted.

(* unit -> acyclic *)

Definition loop {Σ N : Type} `{EqDecision N} (G : grammar Σ N) (A : N) (α : clause Σ N) : bool :=
  match α with
  | unary A' _ => bool_decide (A' = A)
  | binary A1 A2 _ =>
    (nullable G A2 && bool_decide (A1 = A)) ||
    (nullable G A1 && bool_decide (A2 = A))
  | _ => false
  end.

Definition deloop {Σ N : Type} `{EqDecision N} (G : grammar Σ N) : grammar Σ N := {|
  start := start G;
  P A := filter (λ α, ¬ bool_decide (loop G A α)) (P G A)
|}.

Lemma deloop_nullable {Σ N} `{EqDecision N} (G : grammar Σ N) A :
  nullable (deloop G) A = nullable G A.
Admitted.

Lemma deloop_succ_irrefl {Σ N} `{EqDecision N} (G : grammar Σ N) :
  Irreflexive (succ (deloop G)).
Proof.
  intros A HA.
  inversion HA; subst; clear HA.
  - apply elem_of_list_filter in H. simpl in H. naive_solver.
  - apply elem_of_list_filter in H. simpl in H.
    rewrite deloop_nullable in H0. rewrite H0 in H.
    naive_solver.
  - apply elem_of_list_filter in H. simpl in H.
    rewrite deloop_nullable in H0. rewrite H0 in H.
    naive_solver.
Qed.

Lemma deloop_succ_subrel {Σ N} `{EqDecision N} (G : grammar Σ N) :
  subrelation (succ (deloop G)) (succ G).
Proof.
  intros A B HAB.
  destruct HAB; apply elem_of_list_filter in H; destruct H as [_ ?].
  - eapply succ_unary; eauto.
  - eapply succ_left; eauto. by rewrite -deloop_nullable.
  - eapply succ_right; eauto. by rewrite -deloop_nullable.
Qed.

Lemma ex_loop_subrelation {A} (R1 R2 : relation A) x :
  subrelation R1 R2 →
  ex_loop R1 x → ex_loop R2 x.
Admitted.

Theorem deloop_acyclic {Σ N} `{EqDecision N} (G : grammar Σ N) :
  unit G → acyclic (deloop G).
Proof.
  unfold unit, acyclic. intros HG [A HA].
  inversion HA as [? B]; subst; clear HA.
  apply HG. exists A, B. repeat split.
  * intros ->. eapply deloop_succ_irrefl; eauto.
  * by apply deloop_succ_subrel.
  * eapply ex_loop_subrelation. apply deloop_succ_subrel. done.
Qed.

Lemma deloop_valid {Σ N} `{!EqDecision N} (G : grammar Σ N) t A w :
  t ▷ A ={deloop G}=> w →
  ✓{G} t.
Proof.
  intros [? [? Ht]].
  generalize dependent A.
  generalize dependent w.
  induction Ht => w ? B ?.
  all: apply elem_of_list_filter in H; destruct H as [_ ?].
  - by constructor.
  - by constructor.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Definition inf_amb_cond {Σ N : Type} `{EqDecision N} (G : grammar Σ N) (A : N) (w : sentence Σ) : Prop :=
  ∃ C w', reachable G A w C w' ∧ G ⊨ C ⇒ w' ∧
    ((∃ φ, G ⊢ C ↦ unary C φ ∧ (w' ≠ [] → φ w')) ∨
     (∃ E φ, G ⊢ C ↦ binary C E φ ∧ nullable G E = true) ∨
     (∃ E φ, G ⊢ C ↦ binary E C φ ∧ nullable G E = true)).

Lemma sentence_amb_reachable {Σ N} (G : grammar Σ N) A w B w' :
  reachable G A w B w' →
  sentence_ambiguous G B w' →
  sentence_ambiguous G A w.
Admitted.

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

Lemma inf_amb_implies_amb {Σ N} `{EqDecision N} (G : grammar Σ N) A w : 
  inf_amb_cond G A w → sentence_ambiguous G A w.
Proof.
  move => [C [w' [Hr [[t [? [? ?]]] H]]]].
  destruct H as [[φ [? ?]] | [[E [φ [? HE]]] | [E [φ [? HE]]]]].
  - eapply sentence_amb_reachable; first apply Hr.
    exists t, (unary_tree C t). split => //.
    split. repeat split => //. econstructor; naive_solver.
    apply strict_subtree_ne_unary.
  - eapply sentence_amb_reachable; first apply Hr.
    apply nullable_spec in HE. destruct HE as [tε [? [? ?]]].
    exists t, (binary_tree C t tε). split => //.
    split. repeat split => /=. by rewrite H1 app_nil_r.
    econstructor; naive_solver.
    apply strict_subtree_ne_binary_left.
  - eapply sentence_amb_reachable; first apply Hr.
    apply nullable_spec in HE. destruct HE as [tε [? [? ?]]].
    exists t, (binary_tree C tε t). split => //.
    split. repeat split => /=. by rewrite H1 app_nil_l.
    econstructor; naive_solver.
    apply strict_subtree_ne_binary_right.
Qed.

Global Instance valid_decidable Σ N (G : grammar Σ N) t : Decision (✓{G} t).
Admitted.

Lemma deloop_invalid {Σ N} `{!EqDecision N} (G : grammar Σ N) t A w :
  t ▷ A ={G}=> w →
  ¬ ✓{deloop G} t →
  inf_amb_cond G A w.
Proof.
  move => [? [? H]] Hnot.
  generalize dependent w.
  generalize dependent A.
  induction t as [| B [a p] | B t IHt | B t1 IHt1 t2 IHt2 ] => A ? w ?.
  all: inversion H; subst; clear H => /=.
  - exfalso. apply Hnot. constructor.
    eapply elem_of_list_filter. naive_solver.
  - exfalso. apply Hnot. constructor.
    eapply elem_of_list_filter. naive_solver.
  - destruct (decide (✓{deloop G} t)).
    + (* valid *)
      have He : B = root t.
      { eapply bool_decide_eq_true. apply not_false_iff_true. move => He.
        apply Hnot. econstructor; eauto.
        eapply elem_of_list_filter. apply bool_decide_eq_false in He.
        naive_solver. }
      exists (root t), (sentence_of t).
      repeat split => //. rewrite He; constructor. by exists t; repeat split.
      left. exists φ. naive_solver.
    + (* not valid *)
      edestruct IHt as [C [w' [? ?]]]; eauto.
      exists C, w'. split; last done.
      econstructor; eauto.
  - destruct (decide (✓{deloop G} t2)); first destruct (decide (✓{deloop G} t1)).
    + (* both valid *)
      have He : (nullable G (root t2) && bool_decide (root t1 = B)) ||
      (nullable G (root t1) && bool_decide (root t2 = B)) = true.
      { apply not_false_iff_true. move => He. apply Hnot.
        econstructor; eauto.
        eapply elem_of_list_filter. simpl. rewrite He. naive_solver. }
      exists B, (sentence_of t1 ++ sentence_of t2).
      repeat split => //. constructor. exists (binary_tree B t1 t2).
      repeat split. econstructor; eauto.
      right. destruct (orb_true_elim _ _ He) as [H|H].
      all: destruct (andb_prop _ _ H) as [H1 H2].
      all: apply bool_decide_eq_true in H2.
      * left. exists (root t2), φ. naive_solver.
      * right. exists (root t1), φ. naive_solver.
    + (* t1 not valid *)
      edestruct IHt1 as [C [w' [? ?]]]; eauto.
      exists C, w'. split; last done.
      eapply reachable_left; eauto. by eexists; repeat split.
    + (* t2 not valid *)
      edestruct IHt2 as [C [w' [? ?]]]; eauto.
      exists C, w'. split; last done.
      eapply reachable_right; eauto. by eexists; repeat split.
Qed.

Theorem deloop_amb {Σ N} `{EqDecision N} (G : grammar Σ N) A w :
  sentence_ambiguous G A w ↔
    sentence_ambiguous (deloop G) A w ∨ inf_amb_cond G A w.
Proof.
  split.
  - intros [t1 [t2 [[? [? Ht1]] [[? [? Ht2]] Hne]]]].
    destruct (decide (✓{deloop G} t2)); first destruct (decide (✓{deloop G} t1)).
    + (* both valid *) left. exists t1, t2. by repeat split.
    + (* t1 not valid *) right. eapply deloop_invalid; eauto. by repeat split.
    + (* t2 not valid *) right. eapply deloop_invalid; eauto. by repeat split.
  - intros [H|H].
    + destruct H as [t1 [t2 [[? [? Ht1]] [[? [? Ht2]] Hne]]]].
      exists t1, t2. repeat split => //.
      all: by eapply deloop_valid; repeat split.
    + by apply inf_amb_implies_amb.
Qed.
