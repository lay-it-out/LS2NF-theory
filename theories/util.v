From stdpp Require Import relations.
From Coq Require Import ssreflect.

Definition or_relation {A B : Type} (R1 : relation A) (R2 : relation B) : relation (A * B) :=
  λ x y, R1 x.1 y.1 ∨ (x.1 = y.1 ∧ R2 x.2 y.2).

Lemma or_relation_wf {A B : Type} (R1 : relation A) (R2 : relation B) :
  wf R1 →
  wf R2 →
  wf (or_relation R1 R2).
Proof.
  intros HR1 HR2 [a b].
  generalize dependent b.
  induction a as [a IHa] using (well_founded_induction HR1).
  induction b as [b IHb] using (well_founded_induction HR2).
  constructor => [[a' b'] [|]]; naive_solver.
Qed.

Fixpoint nat_range (n : nat) :=
  match n with
  | 0 => []
  | S n' => nat_range n' ++ [n]
  end.

Lemma nat_range_length n :
  length (nat_range n) = n.
Proof.
  induction n => //=.
  rewrite app_length /=. lia.
Qed.

Lemma nat_range_lookup n i :
  i < n →
  nat_range n !! i = Some (S i).
Proof.
  intros. induction n; first lia.
  simpl. destruct (decide (i = n)) as [->|].
  - rewrite lookup_app_r nat_range_length //.
    by rewrite Nat.sub_diag.
  - have ? : i < n by lia.
    rewrite lookup_app_l ?nat_range_length; naive_solver.
Qed.

Lemma nat_range_elem_of n x :
  x ∈ nat_range n → 0 < x ≤ n.
Proof.
  intros Hx. apply elem_of_list_lookup in Hx as [i Hi].
  have ? : i < n.
  { rewrite <- nat_range_length. eapply lookup_lt_Some; eauto. }
  rewrite nat_range_lookup in Hi => //.
  inversion Hi; subst; clear Hi. lia.
Qed.

(* TODO: merge index_range with nat_range *)
Fixpoint index_range (n : nat) :=
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
  i < n →
  index_range n !! i = Some i.
Proof.
  intros. induction n; first lia.
  simpl. destruct (decide (i = n)) as [->|].
  - rewrite lookup_app_r index_range_length //.
    by rewrite Nat.sub_diag.
  - have ? : i < n by lia.
    rewrite lookup_app_l ?index_range_length; naive_solver.
Qed.

Lemma index_range_elem_of n x :
  x ∈ index_range n → 0 ≤ x < n.
Proof.
  intros Hx. apply elem_of_list_lookup in Hx as [i Hi].
  have ? : i < n.
  { rewrite <- index_range_length. eapply lookup_lt_Some; eauto. }
  rewrite index_range_lookup in Hi => //.
  inversion Hi; subst; clear Hi. lia.
Qed.

Program Fixpoint big_or {A : Type} (l : list A) (P : {x : A & x ∈ l} → bool) : bool :=
    match l with
    | [] => false
    | x :: xs => P (existT x _) || big_or xs (λ y,
      match y with existT x Hx => P (existT x _) end)
    end.
  Next Obligation.
    intros. subst. apply elem_of_cons. by left.
  Qed.
  Next Obligation.
    intros. subst. apply elem_of_cons. by right.
  Qed.

Lemma big_or_true {A : Type} (l : list A) (P : {x : A & x ∈ l} → bool) :
  big_or l P = true ↔ ∃ p, P p = true.
Proof.
  induction l => /=.
  - split; first done.
    intros [[? ?] ?]. exfalso. eapply elem_of_nil; eauto.
  - rewrite orb_true_iff.
Admitted.

Program Definition when (P : Prop) `{Decision P} (body : P → bool) : bool :=
  match bool_decide P with
  | true => body _
  | false => false
  end.
Next Obligation.
  intros. eapply bool_decide_eq_true. done.
Qed.

Lemma when_true P `{Decision P} b :
  when P b = true ↔ ∃ HP : P, b HP = true.
Proof.
Admitted.
