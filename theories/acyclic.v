From stdpp Require Import relations.
From Coq Require Import ssreflect.
From ambig Require Import grammar reachable.

(* On the graph representation of the grammar: direct edge *)
Inductive succ {Σ N : Type} (G : grammar Σ N) : relation N :=
  | succ_unary A B φ :
    A ↦ unary B φ ∈ G →
    succ G A B
  | succ_left A B E φ :
    A ↦ binary B E φ ∈ G →
    nullable G E →
    succ G A B
  | succ_right A B E φ :
    A ↦ binary E B φ ∈ G →
    nullable G E →
    succ G A B
  .

(* On graph: do not have non-trivial cycles (a cycle with min length 2) *)
Definition unit {Σ N : Type} (G : grammar Σ N) : Prop :=
  ¬ ∃ A B, A ≠ B ∧ succ G A B ∧ ex_loop (succ G) B.

(* every grammar can be unitized *)

(* acyclic *)

Definition acyclic {Σ N : Type} (G : grammar Σ N) : Prop :=
  ¬ ∃ A, ex_loop (succ G) A.

Fact acyclic_succ_flip_wf {Σ N} (G : grammar Σ N) :
  acyclic G → wf (flip (succ G)).
Admitted.

(* unit -> acyclic *)

Definition deloop {Σ N : Type} `{EqDecision N} (G : grammar Σ N) : grammar Σ N := {|
  start := start G;
  ε_productions := ε_productions G;
  atom_productions := atom_productions G;
  unary_productions A B :=
    if bool_decide (B = A) then None else unary_productions G A B;
  binary_productions A Bl Br :=
    if bool_decide ((nullable G Br ∧ Bl = A) ∨ (nullable G Bl ∧ Br = A))
    then None else binary_productions G A Bl Br;
  unary_predicate_axiom := unary_predicate_axiom G;
  binary_predicate_axiom := binary_predicate_axiom G;
|}.

Fact deloop_nullable {Σ N} `{EqDecision N} (G : grammar Σ N) A :
  nullable (deloop G) A = nullable G A.
Admitted.

Lemma deloop_succ_irrefl {Σ N} `{EqDecision N} (G : grammar Σ N) :
  Irreflexive (succ (deloop G)).
Proof.
  intros A HA.
  inversion HA; subst; clear HA.
  - inversion H. by case_bool_decide.
  - rewrite deloop_nullable in H0. inversion H.
    case_bool_decide => //. naive_solver.
  - rewrite deloop_nullable in H0. inversion H.
    case_bool_decide => //. naive_solver.
Qed.

Lemma deloop_production_subset {Σ N} `{EqDecision N} (G : grammar Σ N) p :
  p ∈ (deloop G) → p ∈ G.
Proof.
  intros Hp. destruct p as [A α]; destruct α => //.
  all: inversion Hp; by case_bool_decide.
Qed.

Lemma deloop_succ_subrel {Σ N} `{EqDecision N} (G : grammar Σ N) :
  subrelation (succ (deloop G)) (succ G).
Proof.
  intros A B HAB. destruct HAB.
  all: apply deloop_production_subset in H.
  all: try rewrite deloop_nullable in H0.
  - eapply succ_unary; eauto.
  - eapply succ_left; eauto.
  - eapply succ_right; eauto.
Qed.

Fact ex_loop_subrelation {A} (R1 R2 : relation A) x :
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

Lemma deloop_valid {Σ N} `{!EqDecision N} (G : grammar Σ N) (t : tree Σ N) A w :
  t ▷ A ={deloop G}=> w →
  ✓{G} t.
Proof.
  generalize dependent A.
  generalize dependent w.
  induction t => w A [? [? Ht]].
  - apply valid_ε_tree_inv in Ht.
    apply deloop_production_subset in Ht.
    by apply valid_ε_tree.
  - apply valid_token_tree_inv in Ht.
    apply deloop_production_subset in Ht.
    by apply valid_token_tree.
  - apply valid_unary_tree_inv in Ht as [φ [Hp [? ?]]].
    apply deloop_production_subset in Hp.
    eapply valid_unary_tree; eauto.
    eapply IHt; by repeat split.
  - apply valid_binary_tree_inv in Ht as [φ [Hp [? [? ?]]]].
    apply deloop_production_subset in Hp.
    eapply valid_binary_tree; eauto.
    eapply IHt1; by repeat split.
    eapply IHt2; by repeat split.
Qed.

Definition inf_amb_cond {Σ N : Type} `{EqDecision N} (G : grammar Σ N) (A : N) (w : sentence Σ) : Prop :=
  ∃ C w', reachable G A w C w' ∧ G ⊨ C ⇒ w' ∧
    ((∃ φ, C ↦ unary C φ ∈ G ∧ φ w') ∨
     (∃ E φ, C ↦ binary C E φ ∈ G ∧ nullable G E) ∨
     (∃ E φ, C ↦ binary E C φ ∈ G ∧ nullable G E)).

Lemma inf_amb_implies_derive_amb {Σ N} `{EqDecision N} (G : grammar Σ N) A w : 
  inf_amb_cond G A w → derive_amb G A w.
Proof.
  move => [C [w' [Hr [[t [Hrt [? ?]]] H]]]].
  destruct H as [[φ [? ?]] | [[E [φ [? HE]]] | [E [φ [? HE]]]]].
  all: eapply reachable_derive_amb; first apply Hr.
  - exists t, (unary_tree C t).
    split; first done.
    split; last apply strict_subtree_ne_unary. 
    repeat split => //.
    eapply valid_unary_tree; naive_solver.
  - apply nullable_spec in HE as [tε [? [? ?]]].
    exists t, (binary_tree C t tε).
    split; first done.
    split; last apply strict_subtree_ne_binary_left.
    repeat split => //.
    { simpl. have -> : tree_word tε = [] by done.
      by rewrite app_nil_r. }
    eapply valid_binary_tree; try naive_solver.
    apply (binary_predicate_axiom G). naive_solver.
  - apply nullable_spec in HE as [tε [? [? ?]]].
    exists t, (binary_tree C tε t).
    split; first done.
    split; last apply strict_subtree_ne_binary_right.
    repeat split => //.
    { simpl. have -> : tree_word tε = [] by done.
      by rewrite app_nil_l. }
    eapply valid_binary_tree; try naive_solver.
    apply (binary_predicate_axiom G). naive_solver.
Qed.

Lemma deloop_invalid {Σ N} `{!EqDecision N} (G : grammar Σ N) (t : tree Σ N) A w :
  t ▷ A ={G}=> w →
  ¬ ✓{deloop G} t →
  inf_amb_cond G A w.
Proof.
  move => [? [? Ht]] Hnot.
  generalize dependent w.
  generalize dependent A.
  induction t as [| B [a p] | B t IHt | B t1 IHt1 t2 IHt2 ] => A HA w Hw.
  all: simpl in HA; simpl in Hw; subst.
  - apply valid_ε_tree_inv in Ht.
    exfalso. by apply Hnot, valid_ε_tree.
  - apply valid_token_tree_inv in Ht.
    exfalso. by apply Hnot, valid_token_tree.
  - apply valid_unary_tree_inv in Ht as [φ [? [? ?]]].
    destruct (✓{deloop G} t) eqn:Heqn.
    + (* valid *) clear IHt.
      have He : root t = A.
      { eapply bool_decide_eq_true. apply not_false_iff_true. move => He.
        apply Hnot. simpl. rewrite He H.
        apply Is_true_andb. naive_solver. }
      exists (root t), (word t).
      split; first by constructor; naive_solver.
      split; first by exists t; repeat split.
      left. exists φ. naive_solver.
    + (* not valid *)
      edestruct IHt as [C [w' [? ?]]]; eauto.
      exists C, w'. split; last done.
      econstructor; naive_solver.
  - apply valid_binary_tree_inv in Ht as [φ [? [? [? ?]]]].
    destruct (✓{deloop G} t2) eqn:Heqn2; first destruct (✓{deloop G} t1) eqn:Heqn1.
    + (* both valid *) clear IHt1 IHt2.
      have He : (nullable G (root t2) ∧ root t1 = A) ∨
        (nullable G (root t1) ∧ root t2 = A).
      { eapply bool_decide_eq_true. apply not_false_iff_true. move => He.
        apply Hnot. simpl. rewrite He H.
        apply Is_true_andb. naive_solver. }
      exists A, (word t1 ++ word t2). repeat split.
      * constructor; naive_solver.
      * exists (binary_tree A t1 t2). repeat split. eapply valid_binary_tree; eauto.
      * right. destruct He as [[? ?] | [? ?]].
        ** left. exists (root t2), φ. naive_solver.
        ** right. exists (root t1), φ. naive_solver.
    + (* t1 not valid *)
      edestruct IHt1 as [C [w' [? ?]]]; eauto.
      exists C, w'. split; last done.
      eapply reachable_left; eauto.
      by eexists; repeat split.
    + (* t2 not valid *)
      edestruct IHt2 as [C [w' [? ?]]]; eauto.
      exists C, w'. split; last done.
      eapply reachable_right; eauto.
      by eexists; repeat split.
Qed.

Theorem deloop_derive_amb {Σ N} `{EqDecision N} (G : grammar Σ N) A w :
  derive_amb G A w ↔
    derive_amb (deloop G) A w ∨ inf_amb_cond G A w.
Proof.
  split.
  - intros [t1 [t2 [[? [? Ht1]] [[? [? Ht2]] Hne]]]].
    destruct (✓{deloop G} t2) eqn:Heqn2; first destruct (✓{deloop G} t1) eqn:Heqn1.
    + (* both valid *) left.
      exists t1, t2. repeat split; naive_solver.
    + (* t1 not valid *) right.
      apply (deloop_invalid G t1); first done.
      by apply Is_true_false.
    + (* t2 not valid *) right.
      apply (deloop_invalid G t2); first done.
      by apply Is_true_false.
  - intros [H|H].
    + destruct H as [t1 [t2 [[? [? Ht1]] [[? [? Ht2]] Hne]]]].
      exists t1, t2. repeat split => //.
      all: by eapply deloop_valid.
    + by apply inf_amb_implies_derive_amb.
Qed.
