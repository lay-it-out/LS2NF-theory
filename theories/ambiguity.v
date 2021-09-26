From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From ambig Require Import grammar reachable.

(* similarity *)

(* assume input trees have same root and word *)

Definition similar {Σ N : Type} (t1 t2 : tree Σ N) : Prop :=
  match t1, t2 with
  | ε_tree _, ε_tree _ => True
  | token_tree R1 tk1, token_tree R2 tk2 => tk1 = tk2
  | unary_tree R1 t1, unary_tree R2 t2 => root t1 = root t2
  | binary_tree R1 tA1 tB1, binary_tree R2 tA2 tB2 =>
    root tA1 = root tA2 ∧ root tB1 = root tB2 ∧ word tA1 = word tA2
  | _, _ => False
  end.

Lemma similar_refl Σ N :
  Reflexive (@similar Σ N).
Proof.
  move => t.
  destruct t => //=.
Qed.

(* local ambiguity *)

Definition local_amb {Σ N : Type} `{EqDecision N} `{EqDecision (token Σ)}
  (G : grammar Σ N) A w : Prop :=
  ∃ H h, reachable G A w H h ∧
    ∃ t1 t2, t1 ▷ H ={G}=> h ∧ t2 ▷ H ={G}=> h ∧ ¬ (similar t1 t2).

(* first direction : local ambiguous -> derivation ambiguous *)

Lemma local_amb_implies_derive_amb {Σ N} `{EqDecision N} `{EqDecision (token Σ)}
  (G : grammar Σ N) A w :
  local_amb G A w → derive_amb G A w.
Proof.
  intros [H [h [Hr [t1 [t2 [Ht1 [Ht2 Hnot]]]]]]].
  eapply reachable_derive_amb; first apply Hr.
  exists t1, t2. split; first done. split; first done.
  intros <-. apply Hnot, similar_refl.
Qed.

(* second direction : derivation ambiguous -> local ambiguous *)

(* diff two trees with same root and sentence *)
Fixpoint diff {Σ N : Type} `{!EqDecision N} `{!EqDecision (token Σ)}
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
    if bool_decide (root tl1 = root tl2 ∧ root tr1 = root tr2 ∧ word tl1 = word tl2)
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
  word t1 = word t2 →
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
  word t1 = word t2 →
  diff t1 t2 = Some (t1', t2') →
  root t1' = root t2' ∧ word t1' = word t2'.
Proof.
  generalize dependent t2.
  induction t1 => t2.
  all: destruct t2 => //= -> Hw Hdiff.
  all: inversion Hdiff; subst; clear Hdiff => //.
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

Lemma derive_amb_implies_local_amb {Σ N} `{EqDecision N} `{EqDecision (token Σ)}
  (G : grammar Σ N) A w :
  derive_amb G A w → local_amb G A w.
Proof.
  intros [t1 [t2 [[Hr1 [Hw1 ?]] [[? [? ?]] ?]]]].
  have [[t1' t2'] Hdiff] : is_Some (diff t1 t2).
  { apply not_eq_None_Some. intros Hcontra. apply diff_None in Hcontra => //.
    all: congruence. }
  have [Hsub1 Hsub2] := (diff_result_subtree _ _ _ _ Hdiff).
  exists (root t1'), (word t1').
  split; first by rewrite -Hr1 -Hw1; apply subtree_reachable.
  exists t1', t2'.
  have [? ?] : root t1' = root t2' ∧ word t1' = word t2'.
  { eapply diff_Some_inv; last eauto. all: congruence. }
  repeat split => //.
  1,2: eapply subtree_valid; eauto.
  eapply diff_result_not_similar; eauto.
Qed.

(* To sum up *)

Theorem derive_amb_iff_local_amb {Σ N} `{EqDecision N} `{EqDecision (token Σ)}
  (G : grammar Σ N) A w :
  derive_amb G A w ↔ local_amb G A w.
Proof.
  split; [ apply derive_amb_implies_local_amb
         | apply local_amb_implies_derive_amb ].
Qed.
