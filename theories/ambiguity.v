From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From LS2NF Require Import grammar sub_derive.

Section ambiguity.

  Context {Σ N : Type}.
  Implicit Type t s T : @tree Σ N.

  Open Scope grammar_scope.

  (** * Similarity of Parse Trees *)

  (** Similarity: two parse trees are similar if they have the same root and the same word. *)
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
    intros t. by destruct t.
  Qed.

  Context `{!EqDecision Σ} `{!EqDecision N}.
  Context (G : grammar Σ N).

  (** * Two Notions of Ambiguity *)
  
  (** Derivation ambiguity: standard notion of ambiguity. *)
  Definition derive_amb A w : Prop :=
    ∃ t1 t2, t1 ▷ A ={G}=> w ∧ t2 ▷ A ={G}=> w ∧ t1 ≠ t2.

  (** Our notion of _local ambiguity_ (Definition 4.4). *)
  Definition local_amb A w : Prop :=
    ∃ H h, reachable G (A, w) (H, h) ∧
      ∃ t1 t2, t1 ▷ H ={G}=> h ∧ t2 ▷ H ={G}=> h ∧ ¬ (similar t1 t2).

  (** * They Are Equal *)
  
  (** We first show: local ambiguity → derivation ambiguity. *)
  
  (** We start by defining a function that substitutes [s] for a subtree [t] in tree [T]. *)
  Fixpoint replace T t s :=
    match T with
    | unary_tree A t1 =>
      if bool_decide (T = t) then Some s else
      t1' ← replace t1 t s; Some (unary_tree A t1')
    | binary_tree A tl tr =>
      if bool_decide (T = t) then Some s else
      match replace tl t s with
      | Some tl' => Some (binary_tree A tl' tr)
      | None => tr' ← replace tr t s; Some (binary_tree A tl tr')
      end
    | _ => if bool_decide (T = t) then Some s else None
    end.

  Lemma bind_Some_is_Some A B (f : A → B) mx :
    is_Some (mx ≫= (λ x, Some (f x))) ↔ is_Some mx.
  Proof.
    unfold is_Some. setoid_rewrite bind_Some. naive_solver.
  Qed.

  Lemma replace_Some T t s :
    subtree t T → is_Some (replace T t s).
  Proof.
    induction T as [?|??|?? IHt|?? IHt1 ? IHt2] => Ht /=.
    - apply subtree_ε_inv in Ht as ->. by case_bool_decide.
    - apply subtree_token_inv in Ht as ->. by case_bool_decide.
    - apply subtree_unary_inv in Ht as [->|?]; case_bool_decide => //.
      apply bind_Some_is_Some. by apply IHt.
    - apply subtree_binary_inv in Ht as [->|[Ht|Ht]]; case_bool_decide => //; case_match => //.
      + apply IHt1 in Ht. by invert Ht.
      + apply bind_Some_is_Some. by apply IHt2.
  Qed.

  Local Ltac simpl_bind_eq_Some :=
    repeat match goal with
    | |- Some _ = Some _ → _ =>
      let H := fresh in intros H; apply Some_inj in H; revert H
    | |- _ ≫= (λ _, Some _) = Some _ → _ =>
      let H := fresh in rewrite bind_Some; intros [? [? H]]; revert H
    | |- (_, _) = (_, _) → _ => inversion 1; subst
    | |- _ = _ → _ => intros ?; subst
    end.

  Lemma replace_id T t s :
    replace T t s = Some T → s = t.
  Proof.
    induction T => /=.
    all: case_bool_decide; try case_match; simpl_bind_eq_Some => //.
    all: naive_solver.
  Qed.

  Lemma replace_witness T t s T' A w H h :
    T ▷ A ={G}=> w →
    t ▷ H ={G}=> h →
    s ▷ H ={G}=> h →
    replace T t s = Some T' →
    T' ▷ A ={G}=> w.
  Proof.
    intros [? [? HT]] [? [? ?]] ?.
    generalize dependent T'.
    generalize dependent w.
    generalize dependent A.
    induction T as [?|??|? ? IHT|?? IHT1 ? IHT2] => T' w ? A ? /=.
    all: case_bool_decide; try case_match; simpl_bind_eq_Some => //=.
    all: invert HT.
    - specialize (IHT (ltac:(done)) _ (ltac:(reflexivity)) _ (ltac:(reflexivity)) _ (ltac:(done))) as [Hr [Hw ?]].
      repeat split => //=.
      econstructor => //; rewrite ?Hr ?Hw; eauto.
    - specialize (IHT1 (ltac:(done)) _ (ltac:(reflexivity)) _ (ltac:(reflexivity)) _ (ltac:(done))) as [Hr [Hw ?]].
      repeat split => //=. { by rewrite Hw. }
      econstructor => //; rewrite ?Hr ?Hw; eauto.
    - specialize (IHT2 (ltac:(done)) _ (ltac:(reflexivity)) _ (ltac:(reflexivity)) _ (ltac:(done))) as [Hr [Hw ?]].
      repeat split => //=. { by rewrite Hw. }
      econstructor => //; rewrite ?Hr ?Hw; eauto.
  Qed.

  Lemma replace_subtree T t s T' :
    replace T t s = Some T' → subtree s T'.
  Proof.
    generalize dependent T'.
    induction T as [?|??|?? IHt|?? IHt1 ? IHt2] => T' /=.
    all: case_bool_decide; try case_match; simpl_bind_eq_Some => //=.
    - eapply rtc_r; first by apply IHt. constructor.
    - eapply rtc_r; first by apply IHt1. constructor.
    - eapply rtc_r; first by apply IHt2. constructor.
  Qed.

  Lemma local_amb_implies_derive_amb A w :
    local_amb A w → derive_amb A w.
  Proof.
    (** Proof outline:
        Let [(H, h)] be a signature such that [Hr: reachable G (A, w) (H, h)].
        Let [t_1] and [t_2] be two dissimilar ([Hnot: ¬ similar t1 t2]) parse trees that both
        [▷ H ={ G }=> h]. *)
    intros [H [h [Hr [t1 [t2 [Ht1 [Ht2 Hnot]]]]]]].
    (** By [reachable_spec], there exist [t] such that [Ht: t ▷ A ={ G }=> w] and that
        [Hsub: subtree t_1 t]. *)
    apply reachable_spec in Hr; last by exists t1.
    specialize (Hr _ Ht1) as [t [Ht Hsub]].
    (** By substituting [t_2] for [t_1] in [t], we obtain a new parse tree [t']. *)
    edestruct (replace_Some _ _ t2 Hsub) as [t' ?].
    (** We claim that [t'] and [t] are the two trees that witness the ambiguity. *)
    exists t', t.
    (** To see this, first of all [t ▷ A ={ G }=> w] is exactly [Ht]. *)
    split; last (split; first done).
    (** Then [t' ▷ A ={ G }=> w] is true from the property of substitution. *)
    - eapply replace_witness; last done. all: done.
    (** Finally, they are not similar. *)
    - intros <-.
      have ? : t2 = t1 by eapply replace_id; eauto.
      subst. apply Hnot, similar_refl.
  Qed.

  (** We then show: derivation ambiguity → local ambiguity. *)

  (* Tree difference: given two trees with the same root and word, compare their node pairs in a 
     depth-first order and immediately return the node pair that is found different. *)
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
      all: case_bool_decide => //; try case_match; eauto.
      naive_solver.
    - generalize dependent t2.
      induction t1 => t2.
      all: destruct t2 => //=; do 2 (inversion 1; subst).
      all: try case_bool_decide; try case_match => //=.
      all: inversion 1; subst; try done; naive_solver.
  Qed.

  Lemma diff_Some_inv t1 t2 t1' t2' :
    root t1 = root t2 →
    word t1 = word t2 →
    diff t1 t2 = Some (t1', t2') →
    root t1' = root t2' ∧ word t1' = word t2'.
  Proof.
    generalize dependent t2.
    induction t1 as [?|??|?? IHt|? t11 IHt1 t12 IHt2] => t2.
    all: destruct t2 as [?|??|??|? t21 t22] => //= -> Hw.
    all: try case_bool_decide; try case_match.
    all: simpl_bind_eq_Some => //.
    3: have Heq : word t11 = word t21 by naive_solver.
    3: rewrite Heq in Hw.
    all: naive_solver.
  Qed.

  Lemma diff_result_not_similar t1 t2 t1' t2' :
    diff t1 t2 = Some (t1', t2') → ¬ (similar t1' t2').
  Proof.
    generalize dependent t2.
    induction t1 => t2 /=.
    all: repeat case_match; try case_bool_decide => //.
    all: simpl_bind_eq_Some => //=.
    all: naive_solver.
  Qed.

  Lemma diff_result_subtree t1 t2 t1' t2' :
    diff t1 t2 = Some (t1', t2') → subtree t1' t1 ∧ subtree t2' t2.
  Proof.
    generalize dependent t2.
    induction t1 as [?|??|?? IHt|?? IHt1 ? IHt2] => t2 /=.
    all: repeat case_match; try case_bool_decide => //.
    all: simpl_bind_eq_Some => //=.
    1: edestruct IHt; eauto.
    2: edestruct IHt1; eauto.
    3: edestruct IHt2; eauto.
    all: split; etrans; eauto.
    all: apply rtc_once; constructor.
  Qed.

  Lemma derive_amb_implies_local_amb A w :
    derive_amb A w → local_amb A w.
  Proof.
    (** Proof outline:
        Let [t_1 ≠ t_2] be the two trees that witness the ambiguity. *)
    intros [t1 [t2 [[Hr1 [Hw1 ?]] [[? [? ?]] ?]]]].
    (** Applying the [diff] algorithm we obtain two subtrees, say [t_1'] from [t_1] and
        [t_2'] from [t_2] *)
    have [[t1' t2'] Hdiff] : is_Some (diff t1 t2).
    { apply not_eq_None_Some. intros Hcontra. apply diff_None in Hcontra => //.
      all: congruence. }
    have [Hsub1 Hsub2] := (diff_result_subtree _ _ _ _ Hdiff).
    (** We have [t1'] is valid. *)
    have Ht1' : t1' ▷ root t1' ={G}=> word t1'.
    { repeat split. eapply subtree_valid; eauto. }
    (** Pick the root and word of [t1'] as the signature. *)
    exists (root t1'), (word t1'). split.
    (** By the property of substitution, we can show this signature is reachable from [(A, w)]. *)
    - apply reachable_spec; first by exists t1'.
      intros t' Ht'.
      edestruct (replace_Some _ _ t' Hsub1) as [T ?].
      exists T. split; last eapply replace_subtree; eauto.
      eapply replace_witness. 2: apply Ht1'. 2: apply Ht'. 2: eauto.
      by repeat split.
    (** By the property of [diff], we can show [t1'] and [t2'] both witness the chosen signature 
        and that they are not similar. *)
    - exists t1', t2'.
      have [? ?] : root t1' = root t2' ∧ word t1' = word t2'.
      { eapply diff_Some_inv; last eauto. all: congruence. }
      repeat split => //. eapply subtree_valid; eauto.
      eapply diff_result_not_similar; eauto.
  Qed.

  (** Putting the above results together, we obtain Theorem 4.5. *)
  Theorem derive_amb_iff_local_amb A w :
    derive_amb A w ↔ local_amb A w.
  Proof.
    split; [ apply derive_amb_implies_local_amb
           | apply local_amb_implies_derive_amb ].
  Qed.

End ambiguity.

Arguments similar {_} {_}.