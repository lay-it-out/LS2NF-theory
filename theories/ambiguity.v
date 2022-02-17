From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From ambig Require Import grammar sub_derive.

Section ambiguity.

  Context {Σ N : Type}.
  Implicit Type t s T : @tree Σ N.

  Open Scope grammar_scope.

  (* similarity *)

  (* assume input trees have same root and word *)

  Definition similar t1 t2 : Prop :=
    match t1, t2 with
    | ε_tree _, ε_tree _ => True
    | token_tree R1 tk1, token_tree R2 tk2 => tk1 = tk2
    | unary_tree R1 t1, unary_tree R2 t2 => root t1 = root t2
    | binary_tree R1 tA1 tB1, binary_tree R2 tA2 tB2 =>
        root tA1 = root tA2 ∧ root tB1 = root tB2 ∧ word tA1 = word tA2
    | _, _ => False
    end.

  Lemma similar_refl :
    Reflexive similar.
  Proof.
    move => t.
    destruct t => //=.
  Qed.

  Context `{!EqDecision Σ} `{!EqDecision N}.
  Context (G : grammar Σ N).
  
  (* standard notion of ambiguity *)
  Definition derive_amb A w : Prop :=
    ∃ t1 t2, t1 ▷ A ={G}=> w ∧ t2 ▷ A ={G}=> w ∧ t1 ≠ t2.

  (* local ambiguity *)
  Definition local_amb A w : Prop :=
    ∃ H h, reachable G (A, w) (H, h) ∧
      ∃ t1 t2, t1 ▷ H ={G}=> h ∧ t2 ▷ H ={G}=> h ∧ ¬ (similar t1 t2).

  Ltac invert H := inversion H; subst; clear H.

  (* first direction : local ambiguous -> derivation ambiguous *)

  Fixpoint subst T t s :=
    match T with
    | unary_tree A t1 =>
      if bool_decide (T = t) then Some s else
      t1' ← subst t1 t s; Some (unary_tree A t1')
    | binary_tree A tl tr =>
      if bool_decide (T = t) then Some s else
      match subst tl t s with
      | Some tl' => Some (binary_tree A tl' tr)
      | None => tr' ← subst tr t s; Some (binary_tree A tl tr')
      end
    | _ => if bool_decide (T = t) then Some s else None
    end.

  Ltac push_bind :=
    match goal with 
    | [ |- context [ ?x ≫= _ ] ] => destruct x; simpl
    end.

  Lemma subst_Some T t s :
    subtree t T → is_Some (subst T t s).
  Proof.
    intros Ht.
    induction T => /=.
    1: apply subtree_ε_inv in Ht.
    2: apply subtree_token_inv in Ht.
    3: apply subtree_unary_inv in Ht.
    4: apply subtree_binary_inv in Ht.
    all: repeat case_bool_decide.
    all: repeat case_match.
    all: repeat push_bind.
    all: naive_solver.
  Qed.

  Lemma subst_id T t s :
    subst T t s = Some T → s = t.
  Proof.
    induction T => /=.
    all: repeat case_bool_decide => //=.
    all: repeat case_match.
    all: repeat push_bind.
    all: naive_solver.
  Qed.

  Lemma subst_witness T t s T' A w H h :
    T ▷ A ={G}=> w →
    t ▷ H ={G}=> h →
    s ▷ H ={G}=> h →
    subst T t s = Some T' →
    T' ▷ A ={G}=> w.
  Proof.
    intros [? [? ?]] [? [? ?]] Hs.
    generalize dependent A.
    generalize dependent w.
    generalize dependent T'.
    induction T => T' w ? A ? /=.
    all: repeat case_bool_decide => //=.
    all: repeat case_match.
    all: repeat push_bind.
    all: inversion 1; subst => //.
    - invert H2.
      have [Hr [Hw ?]] : t0 ▷ (root T) ={ G }=> (word T) by naive_solver.
      repeat split => //. econstructor => //. by rewrite Hr. by rewrite Hw.
    - invert H2.
      have [Hr [Hw ?]] : t0 ▷ (root T1) ={ G }=> (word T1) by naive_solver.
      repeat split => //. simpl. by rewrite Hw.
      econstructor => //. by rewrite Hr. by rewrite Hw.
    - invert H2.
      have [Hr [Hw ?]] : t0 ▷ (root T2) ={ G }=> (word T2) by naive_solver.
      repeat split => //. simpl. by rewrite Hw.
      econstructor => //. by rewrite Hr. by rewrite Hw.
  Qed.

  Lemma subst_subtree T t s T' :
    subst T t s = Some T' → subtree s T'.
  Proof.
    generalize dependent T'.
    induction T => T' /=.
    all: repeat case_bool_decide => //=.
    all: repeat case_match.
    all: repeat push_bind.
    all: inversion 1; subst => //.
    all: apply rtc_r with (y := t0); [naive_solver | constructor].
  Qed.

  Lemma local_amb_implies_derive_amb A w :
    local_amb A w → derive_amb A w.
  Proof.
    intros [H [h [Hr [t1 [t2 [Ht1 [Ht2 Hnot]]]]]]].
    apply reachable_spec in Hr; last by exists t1.
    specialize (Hr _ Ht1) as [t [Ht Hsub]].
    edestruct (subst_Some _ _ t2 Hsub) as [t' ?].
    exists t', t. split; last split.
    - eapply subst_witness. apply Ht. apply Ht1. apply Ht2. eauto.
    - done.
    - intros <-.
      have ? : t2 = t1 by eapply subst_id; eauto.
      subst. apply Hnot, similar_refl.
  Qed.

  (* second direction : derivation ambiguous -> local ambiguous *)

  (* diff two trees with same root and sentence *)
  Fixpoint diff t1 t2 :=
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

  Lemma diff_None t1 t2 :
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

  Lemma diff_Some_inv t1 t2 t1' t2' :
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

  Lemma diff_result_not_similar t1 t2 t1' t2' :
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

  Lemma diff_result_subtree t1 t2 t1' t2' :
    diff t1 t2 = Some (t1', t2') → subtree t1' t1 ∧ subtree t2' t2.
  Proof.
    generalize dependent t2.
    induction t1 => t2.
    all: destruct t2 => //= Hdiff.
    all: inversion Hdiff; subst; clear Hdiff.
    all: try by split; constructor.
    - case_bool_decide.
      * edestruct IHt1; eauto. split; etrans; eauto.
        all: apply rtc_once; constructor.
      * inversion H0; subst. split; by constructor.
    - case_bool_decide; first case_match.
      * edestruct (IHt1_1 t2_1); eauto; try congruence. split; etrans; eauto.
        all: apply rtc_once; constructor.
      * edestruct (IHt1_2 t2_2); eauto. split; etrans; eauto.
        all: apply rtc_once; constructor.
      * inversion H0; subst. split; by constructor.
  Qed.

  Lemma derive_amb_implies_local_amb A w :
    derive_amb A w → local_amb A w.
  Proof.
    intros [t1 [t2 [[Hr1 [Hw1 ?]] [[? [? ?]] ?]]]].
    have [[t1' t2'] Hdiff] : is_Some (diff t1 t2).
    { apply not_eq_None_Some. intros Hcontra. apply diff_None in Hcontra => //.
      all: congruence. }
    have [Hsub1 Hsub2] := (diff_result_subtree _ _ _ _ Hdiff).
    have Ht1' : t1' ▷ root t1' ={G}=> word t1'.
    { repeat split. eapply subtree_valid; eauto. }
    exists (root t1'), (word t1'). split.
    - apply reachable_spec; first by exists t1'.
      intros t' Ht'.
      edestruct (subst_Some _ _ t' Hsub1) as [T ?].
      exists T. split; last eapply subst_subtree; eauto.
      eapply subst_witness. 2: apply Ht1'. 2: apply Ht'. 2: eauto.
      by repeat split.
    - exists t1', t2'.
      have [? ?] : root t1' = root t2' ∧ word t1' = word t2'.
      { eapply diff_Some_inv; last eauto. all: congruence. }
      repeat split => //. eapply subtree_valid; eauto.
      eapply diff_result_not_similar; eauto.
  Qed.

  (* To sum up *)

  Theorem derive_amb_iff_local_amb A w :
    derive_amb A w ↔ local_amb A w.
  Proof.
    split; [ apply derive_amb_implies_local_amb
           | apply local_amb_implies_derive_amb ].
  Qed.

End ambiguity.

Arguments similar {_} {_}.