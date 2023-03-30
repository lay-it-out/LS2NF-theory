From stdpp Require Import relations sorting.
From Coq Require Import ssreflect.

Ltac invert H := inversion H; subst; clear H.

Fixpoint index_range (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => index_range n' ++ [n']
  end.

Lemma index_range_length n :
  length (index_range n) = n.
Proof.
  induction n => //=.
  rewrite app_length /=. lia.
Qed.

Lemma index_range_lookup n i :
  i < n → index_range n !! i = Some i.
Proof.
  intros. induction n; first lia.
  simpl. destruct (decide (i = n)) as [->|].
  - rewrite lookup_app_r index_range_length //.
    by rewrite Nat.sub_diag.
  - have ? : i < n by lia.
    rewrite lookup_app_l ?index_range_length; naive_solver.
Qed.

Lemma index_range_elem_of n x :
  x ∈ index_range n ↔ x < n.
Proof.
  rewrite elem_of_list_lookup. split.
  - intros [i Hi].
    have ? : i < n.
    { rewrite <- index_range_length. eapply lookup_lt_Some; eauto. }
    rewrite index_range_lookup in Hi => //.
    congruence.
  - intros ?. exists x. by rewrite index_range_lookup.
Qed.

Section Sorted_lemmas.

  Context {A : Type} (R : relation A).

  Definition monotone (l : list A) : Prop :=
    ∀ i j x y, l !! i = Some x → l !! j = Some y → i < j → R x y.
  
  Context `{!Transitive R}.

  Definition monotone_trans_alt (l : list A) : Prop :=
    ∀ i x y, i < length l - 1 → l !! i = Some x → l !! (i + 1) = Some y → R x y.

  Lemma monotone_trans_alt_spec l :
    monotone_trans_alt l → monotone l.
  Proof.
    intros Hm i j x y Hx Hy ?.
    have ? : j < length l by apply lookup_lt_is_Some.
    have [k ?] : ∃ k : nat, j = i + (1 + k) by exists (j - i - 1); lia. subst.
    generalize dependent y.  
    induction k as [|k IHk] => y Hy. { apply (Hm i); [lia | done..]. }
    have [z Hz] : is_Some (l !! (i + (1 + k))) by apply lookup_lt_is_Some; lia.
    etrans. { apply IHk; eauto; lia. }
    apply (Hm (i + (1 + k))); [lia|auto..]. rewrite -Hy; f_equal; lia.
  Qed.

  Lemma Sorted_cons_iff a l :
    Sorted R (a :: l) ↔ (Sorted R l ∧ HdRel R a l).
  Proof.
    split.
    - by apply Sorted_inv.
    - intros [? ?]. by apply Sorted_cons.
  Qed.

  Lemma HdRel_Forall x l :
    Sorted R l → HdRel R x l → Forall (R x) l.
  Proof.
    intros. apply Sorted_extends; eauto.
  Qed.

  Lemma Sorted_monotone l :
    Sorted R l ↔ monotone l.
  Proof.
    induction l as [|a l IHl] => //.
    rewrite Sorted_cons_iff.
    split.
    - intros [Hm Ha] i j x y Hx Hy ?.
      destruct i; simpl in Hx.
      * invert Hx. destruct j; [lia|]. simpl in Hy.
        apply elem_of_list_lookup_2 in Hy.
        eapply Forall_forall; last exact Hy. by apply HdRel_Forall.
      * destruct j; [lia|]. simpl in Hy.
        apply IHl in Hm. eapply Hm; eauto; lia.
    - intros Hm. split.
      * apply IHl. intros i j x y Hx Hy ?. apply (Hm (S i) (S j)) => //. lia.
      * destruct l as [|b l] => //. constructor. apply (Hm 0 1) => //.
  Qed.

End Sorted_lemmas.

Section prefix_lemmas.
  Context {A : Type}.
  Implicit Type l : list A.

  Lemma prefix_refl l :
    l `prefix_of` l.
  Proof. naive_solver. Qed.

  Lemma prefix_app_drop l1 l2 l3 :
    l1 ++ l2 `prefix_of` l3 ↔
    l1 `prefix_of` l3 ∧ l2 `prefix_of` drop (length l1) l3.
  Proof.
    split => H. 1: split.
    - by apply prefix_app_l in H.
    - inversion H; subst. rewrite -app_assoc drop_app. apply prefix_app_r, prefix_refl.
    - destruct H as [H1 H2]. inversion H1; subst. inversion H2; subst.
      apply prefix_app. by rewrite drop_app in H2.
  Qed.

End prefix_lemmas.