From stdpp Require Import list.
From Coq Require Import ssreflect.

Section slice.
  Context {A : Type}.
  Implicit Type l : list A.
  Implicit Type a k : nat.

  Definition slice l a k : list A :=
    take k (drop a l).

  Lemma slice_length l a k :
    a + k ≤ length l → length (slice l a k) = k.
  Proof.
    rewrite take_length drop_length. lia.
  Qed.

  Lemma slice_lookup l a k i :
    (slice l a k) !! i = l !! (a + i).
  Admitted.

  Lemma slice_nil_iff l a k :
    a + k ≤ length l →
    slice l a k = [] ↔ k = 0.
  Proof.
    intros. rewrite -length_zero_iff_nil slice_length //.
  Qed.

  Lemma slice_nil l a :
    a ≤ length l → slice l a 0 = [].
  Proof.
    intros. apply slice_nil_iff; lia.
  Qed.

  Lemma slice_nonempty_iff l a k :
    a + k ≤ length l →
    slice l a k ≠ [] ↔ 0 < k.
  Proof.
    intros. have -> : 0 < k ↔ k ≠ 0 by lia.
    by apply not_iff_compat, slice_nil_iff.
  Qed.

  Lemma slice_singleton_iff l a k x :
    slice l a k = [x] ↔ k = 1 ∧ l !! a = Some x.
  Admitted.

  Lemma slice_singleton l a x :
    l !! a = Some x →
    slice l a 1 = [x].
  Admitted.

  Lemma slice_full_iff l a k :
    a + k ≤ length l → l ≠ [] →
    slice l a k = l ↔ a = 0 ∧ k = length l.
  Proof.
    intros. split.
    - intros Hl. apply (f_equal length) in Hl.
      rewrite slice_length in Hl; first done. lia.
    - intros [-> ->]. by rewrite /slice drop_0 firstn_all.
  Qed.

  Lemma slice_full l k :
    k = length l → slice l 0 k = l.
  Proof.
    intros ->. by rewrite /slice drop_0 firstn_all.
  Qed.

  Lemma slice_cons_Some l l' a k x :
    x :: l' = slice l a k →
    l !! a = Some x.
  Admitted.

  Lemma slice_split l a k h :
    slice l a k = slice l a h ++ slice l (a + h) (k - h).
  Admitted.

  Lemma slice_app_merge_2 l a k1 k2 :
    slice l a k1 ++ slice l (a + k1) k2 = slice l a (k1 + k2).
  Admitted.

  Lemma slice_merge_2 l a k1 k2 :
    slice l (a - k1) k1 ++ slice l a k2 = slice l (a - k1) (k1 + k2).
  Admitted.

  Lemma slice_app w x δ δ' :
    slice w x (δ + δ') = slice w x δ ++ slice w (x + δ) δ'.
  Admitted.

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
    l ≠ [] →
    slice l a k = slice l a' k' →
    a' = a ∧ k' = k.
  Admitted.

  Lemma slice_app_inv_NoDup l a k l1 l2 :
    NoDup l →
    l1 ≠ [] →
    l2 ≠ [] →
    slice l a k = l1 ++ l2 →
    l1 = slice l a (length l1) ∧ l2 = slice l (a + length l1) (k - length l1).
  Admitted.

  Lemma slice_app_inv_NoDup_l l a k l1 l2 :
    NoDup l →
    slice l a k = l1 ++ l2 →
    l1 = slice l a (length l1).
  Admitted.

  Lemma slice_app_inv l l' a k k' :
    slice l a k' ++ l' = slice l a k →
    l' = slice l (a + k') (length l').
  Admitted.

  Lemma slice_middle l l1 l' l2 :
    l = l1 ++ l' ++ l2 →
    l' = slice l (length l1) (length l').
  Admitted.

  Definition sublist l' l : Prop :=
    ∃ l1 l2, l = l1 ++ l' ++ l2.

  Lemma sublist_length l' l :
    sublist l' l →
    length l' ≤ length l.
  Admitted.

  Lemma sublist_slice l' l :
    sublist l' l →
    ∃ a, a + length l' ≤ length l ∧ l' = slice l a (length l').
  Admitted.

  (* Lemma slice_app_sublist_NoDup l a1 k1 a2 k2 :
    NoDup l →
    a1 + k1 ≤ length l →
    a2 + k2 ≤ length l →
    0 < k1 →
    0 < k2 →
    sublist (slice l a1 k1 ++ slice l a2 k2) l →
    a2 = a1 + k1 ∧ a1 + k1 + k2 ≤ length l.
  Proof.
    intros Hnd ? ? ? ? Hsub.
    apply sublist_slice in Hsub as [a Ha].
    rewrite app_length !slice_length in Ha.
    destruct Ha as [? Ha].
    have :
        (slice l a1 k1 ++ slice l a2 k2) !! k1 = slice l a (k1 + k2) !! k1
      by rewrite Ha.
    rewrite lookup_app_r ?slice_length ?slice_lookup //.
    rewrite Nat.sub_diag Nat.add_0_r. intros Heq1.
    apply NoDup_lookup_in_range in Heq1 => //; [|lia..].
    have ? : a2 = a1 + k1.
    { have :
        (slice l a1 k1 ++ slice l a2 k2) !! 0 = slice l a (k1 + k2) !! 0
      by rewrite Ha.
      rewrite lookup_app_l ?slice_length ?slice_lookup; first lia.
      rewrite !Nat.add_0_r. intros Heq2.
      apply NoDup_lookup_in_range in Heq2 => //; [|lia..].
      lia.
    }
    split; lia.
  Qed. *)

  Lemma nonempty_sublist_unique_NoDup l' l :
    NoDup l →
    l' ≠ [] →
    sublist l' l →
    exists! a, l' = slice l a (length l').
  Proof.
    intros Hnd Hne [l1 [l2 Hl]].
    apply slice_middle in Hl.
    exists (length l1). split; first done.
    intros a Hl'.
    destruct l' as [|x l']; first done.
    apply slice_cons_Some in Hl.
    apply slice_cons_Some in Hl'.
    eapply NoDup_lookup; eauto.
  Qed.

End slice.
