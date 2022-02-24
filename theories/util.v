From stdpp Require Import relations.
From Coq Require Import ssreflect.

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
