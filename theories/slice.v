From stdpp Require Import list.
From Coq Require Import ssreflect.

Section slice.
  Context {A : Type}.
  Implicit Type l : list A.
  Implicit Type a k : nat.

  Definition slice l a k : list A :=
    take k (drop a l).

  Lemma slice_nil l a :
    slice l a 0 = [].
  Proof.
    by rewrite /slice take_0.
  Qed.

  Lemma slice_full l k :
    k = length l → slice l 0 k = l.
  Proof.
    intros ->. by rewrite /slice drop_0 firstn_all.
  Qed.

  Lemma slice_length l a k :
    a + k ≤ length l → length (slice l a k) = k.
  Proof.
    rewrite take_length drop_length. lia.
  Qed.

  Lemma slice_nil_iff l a k :
    a + k ≤ length l →
    slice l a k = [] ↔ k = 0.
  Proof.
    intros. rewrite -length_zero_iff_nil slice_length //.
  Qed.

  Lemma slice_nonempty_iff l a k :
    a + k ≤ length l →
    slice l a k ≠ [] ↔ 0 < k.
  Proof.
    intros. have -> : 0 < k ↔ k ≠ 0 by lia.
    by apply not_iff_compat, slice_nil_iff.
  Qed.

  Lemma slice_lookup l a k i :
    i < k → (slice l a k) !! i = l !! (a + i).
  Proof.
    intros. by rewrite /slice lookup_take ?lookup_drop.
  Qed.

  Lemma slice_singleton l a x :
    l !! a = Some x → slice l a 1 = [x].
  Proof.
    intros. eapply list_eq_same_length; eauto.
    - have ? : a < length l by apply lookup_lt_is_Some; naive_solver.
      rewrite slice_length //; lia.
    - intros i x' x'' => /= => ?.
      rewrite slice_lookup //.
      have -> : i = 0 by lia.
      rewrite Nat.add_0_r. naive_solver.
  Qed.

  Lemma slice_singleton_iff l a k x :
    a + k ≤ length l →
    slice l a k = [x] ↔ k = 1 ∧ l !! a = Some x.
  Proof.
    intros. split.
    - intros Heq.
      have ? : k = 1.
      { apply (f_equal length) in Heq. by rewrite slice_length in Heq. }
      subst. apply (f_equal (lookup 0)) in Heq. simpl in Heq.
      rewrite slice_lookup in Heq; [lia|]. by rewrite Nat.add_0_r in Heq.
    - intros [-> ?]. by apply slice_singleton.
  Qed.

  Lemma slice_full_iff l a k :
    a + k ≤ length l → l ≠ [] →
    slice l a k = l ↔ a = 0 ∧ k = length l.
  Proof.
    intros. split.
    - intros Hl. apply (f_equal length) in Hl.
      rewrite slice_length in Hl; first done. lia.
    - intros [-> ->]. by rewrite /slice drop_0 firstn_all.
  Qed.

  Lemma slice_app_1 l a k1 k2 :
    slice l a k1 ++ slice l (a + k1) k2 = slice l a (k1 + k2).
  Proof.
    by rewrite /slice -drop_drop take_take_drop.
  Qed.

  Lemma slice_app_2 l a k1 k2 :
    k1 ≤ a →
    slice l (a - k1) k1 ++ slice l a k2 = slice l (a - k1) (k1 + k2).
  Proof.
    intros. have {2}-> : a = (a - k1) + k1 by lia.
    by rewrite slice_app_1.
  Qed.

  Lemma slice_split l a k h :
    h ≤ k →
    slice l a k = slice l a h ++ slice l (a + h) (k - h).
  Proof.
    intros. have {1}-> : k = h + (k - h) by lia.
    by rewrite slice_app_1.
  Qed.

  Lemma slice_eq_inv l a k k' :
    a + k ≤ length l →
    a + k' ≤ length l →
    slice l a k = slice l a k' → k' = k.
  Proof.
    intros ? ? Heq.
    apply (f_equal length) in Heq. rewrite !slice_length in Heq => //.
  Qed.

  Lemma NoDup_lookup_in_range l i j :
    NoDup l →
    i < length l →
    j < length l →
    l !! i = l !! j →
    i = j.
  Proof.
    intros Hnd Hi Hj Heq.
    apply lookup_lt_is_Some in Hi as [x ?].
    apply lookup_lt_is_Some in Hj as [y ?].
    have ? : x = y by congruence. subst.
    eapply NoDup_lookup; eauto.
  Qed.

  Lemma slice_eq_inv_NoDup l a k a' k' :
    NoDup l →
    a + k ≤ length l →
    a' + k' ≤ length l →
    0 < k' →
    slice l a k = slice l a' k' →
    a' = a ∧ k' = k.
  Proof.
    intros ? ? ? ? Heq.
    have ? : k = k'.
    { apply (f_equal length) in Heq. rewrite !slice_length in Heq => //. }
    subst. split => //.
    apply (f_equal (lookup 0)) in Heq.
    rewrite !slice_lookup ?Nat.add_0_r in Heq => //.
    eapply NoDup_lookup_in_range; eauto; lia.
  Qed.

  Lemma slice_app_inv_NoDup_aux l a k a1 k1 a2 k2 :
    NoDup l →
    a + k ≤ length l →
    a1 + k1 ≤ length l →
    a2 + k2 ≤ length l →
    0 < k1 →
    0 < k2 →
    slice l a k = slice l a1 k1 ++ slice l a2 k2 →
    a1 = a ∧ a2 = a1 + k1 ∧ k1 + k2 = k.
  Proof.
    intros ? ? ? ? ? ? Heq.
    have ? : k = k1 + k2.
    { apply (f_equal length) in Heq. rewrite app_length !slice_length in Heq => //. }
    subst.
    have ? : a1 = a.
    { apply (f_equal (lookup 0)) in Heq.
      rewrite lookup_app_l in Heq; first by rewrite slice_length //.
      rewrite !slice_lookup ?Nat.add_0_r in Heq; [lia..|].
      eapply NoDup_lookup_in_range; eauto; lia. }
    subst.
    have ? : a2 = a + k1.
    { apply (f_equal (lookup k1)) in Heq.
      rewrite lookup_app_r in Heq; first by rewrite slice_length.
      rewrite !slice_lookup ?slice_length ?Nat.sub_diag ?Nat.add_0_r in Heq; [lia..|].
      eapply NoDup_lookup_in_range; eauto; lia. }
    naive_solver.
  Qed.

  Ltac normalize_app_assoc :=
    repeat match goal with
    | [ |- context [ (?l1 ++ ?l2) ++ ?l3 ] ] => rewrite -app_assoc
    end.

  Definition sublist l' l : Prop :=
    ∃ l1 l2, l = l1 ++ l' ++ l2.

  Lemma sublist_app_l l l1 l2 :
    sublist (l1 ++ l2) l → sublist l1 l.
  Proof.
    intros [lp [ls Hl]]. exists lp, (l2 ++ ls).
    revert Hl. by normalize_app_assoc.
  Qed.
  
  Lemma sublist_app_r l l1 l2 :
    sublist (l1 ++ l2) l → sublist l2 l.
  Proof.
    intros [lp [ls Hl]]. exists (lp ++ l1), ls.
    revert Hl. by normalize_app_assoc.
  Qed.

  Lemma sublist_slice l' l :
    sublist l' l →
    ∃ a, a + length l' ≤ length l ∧ l' = slice l a (length l').
  Proof.
    intros [l1 [l2 ->]]. exists (length l1). split.
    - rewrite !app_length. lia.
    - by rewrite /slice drop_app take_app.
  Qed.

  Lemma sublist_app_slice_NoDup l l1 l2 :
    NoDup l →
    sublist (l1 ++ l2) l →
    0 < length l1 →
    0 < length l2 →
    ∃ a, a + length l1 + length l2 ≤ length l ∧
      l1 = slice l a (length l1) ∧ l2 = slice l (a + length l1) (length l2).
  Proof.
    intros ? Hl ? ?.
    have Hl1 : sublist l1 l by eapply sublist_app_l; eauto.
    apply sublist_slice in Hl1 as [a1 [? Hl1]].
    have Hl2 : sublist l2 l by eapply sublist_app_r; eauto.
    apply sublist_slice in Hl2 as [a2 [? Hl2]].
    apply sublist_slice in Hl as [a [Hlen Hl]].
    rewrite app_length in Hlen.
    symmetry in Hl. rewrite Hl1 Hl2 in Hl.
    rewrite app_length !slice_length in Hl => //.
    apply slice_app_inv_NoDup_aux in Hl => //.
    naive_solver.
  Qed.

  Lemma slice_sublist l a k :
    a + k ≤ length l → sublist (slice l a k) l.
  Proof.
    intros. exists (slice l 0 a), (slice l (a + k) (length l - a - k)).
    rewrite !slice_app_1.
    have -> : a + (k + (length l - a - k)) = length l by lia.
    by rewrite slice_full.
  Qed.

  Lemma slice_app_inv_NoDup l a k l1 l2 :
    NoDup l →
    a + k ≤ length l →
    slice l a k = l1 ++ l2 →
    l1 = slice l a (length l1) ∧ l2 = slice l (a + length l1) (k - length l1).
  Proof.
    intros ? ? Hl.
    have Hsub : sublist (l1 ++ l2) l. { rewrite -Hl. by apply slice_sublist. }
    destruct l1 as [|x1 l1]; last destruct l2 as [|x2 l2].
    - rewrite app_nil_l in Hl. rewrite slice_nil Nat.add_0_r Nat.sub_0_r //.
    - rewrite app_nil_r in Hl.
      have ? : k = length (x1 :: l1) by rewrite -Hl slice_length.
      subst. rewrite Nat.sub_diag slice_nil //.
    - apply sublist_app_slice_NoDup in Hsub as [a' [Hlen [Hl1 Hl2]]] => //.
      2,3: rewrite cons_length; lia.
      rewrite Hl1 Hl2 in Hl. rewrite cons_length in Hlen.
      apply slice_app_inv_NoDup_aux in Hl as [? [? ?]] => //.
      2-4: rewrite cons_length; lia.
      have -> : k - length (x1 :: l1) = length (x2 :: l2) by lia.
      naive_solver.
  Qed.

End slice.
