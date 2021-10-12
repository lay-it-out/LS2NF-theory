From stdpp Require Import relations.
From Coq Require Import ssreflect.
From ambig Require Import grammar decidability util ambiguity acyclic.

Section encoding.

  Variable Σ N : Type.
  Context `{EqDecision Σ}.
  Context `{EqDecision N}.

  Variable G : grammar Σ N.
  Context `{acyclic G}.

  (* sat model *)

  Record model := {
    term : nat → Σ;
    line : nat → nat;
    col : nat → nat;
    can_derive : N → nat (* start (inclusive) *) → nat (* length *) → bool;
    can_reach_from : N → nat (* start (inclusive) *) → nat (* length *) → bool;
  }.

  Fixpoint decode m x δ : sentence Σ :=
    match δ with
    | 0 => []
    | S n => term m x @ (line m x, col m x) :: decode m (S x) n
    end.

  Lemma decode_length m x δ :
    length (decode m x δ) = δ.
  Proof.
    generalize dependent x.
    induction δ => x //=.
    naive_solver.
  Qed.

  Lemma decode_merge m x δ δ' :
    decode m x δ ++ decode m (x + δ) δ' = decode m x (δ + δ').
  Proof.
    generalize dependent x.
    induction δ as [|n IHn] => x /=.
    - by rewrite -plus_n_O.
    - rewrite <- IHn.
      have -> : x + S n = S x + n by lia.
      done.
  Qed.

  (* formula: a predicate over a model *)

  Definition formula : Type := model → Prop.

  (* encoding derivation *)

  Definition Φ_derive k : formula := λ m,
    ∀ A x δ, 0 < δ (* nonempty *) → x + δ ≤ k →
      can_derive m A x δ = true ↔ Exists (λ α,
        match α with
        | ε => False (* not consider [] *)
        | atom a => δ = 1 ∧ term m x = a
        | unary B φ => apply₁ φ (decode m x δ) = true ∧ can_derive m B x δ = true
        | binary Bl Br φ =>
          (G ⊨ Bl ⇒ [] ∧ can_derive m Br x δ = true) ∨
          (G ⊨ Br ⇒ [] ∧ can_derive m Bl x δ = true) ∨
          (∃ δ', 0 < δ' < δ ∧
            can_derive m Bl x δ' = true ∧
            can_derive m Br (x + δ') (δ - δ') = true ∧
            apply₂ φ (decode m x δ') (decode m (x + δ') (δ - δ')) = true)
        end
      ) (clauses G A).

  Notation "⟨ x , y ⟩" := (existT x y).

  Lemma list_nonempty_length {A} (l : list A) :
    l ≠ [] ↔ 0 < length l.
  Admitted.

  Lemma Φ_derive_spec k m :
    Φ_derive k m →
    ∀ A x δ, 0 < δ → x + δ ≤ k →
      can_derive m A x δ = true ↔ G ⊨ A ⇒ decode m x δ.
  Proof.
    intros HΦ A x δ ? ?. rewrite -check_derive_spec.
    (* induction on range length *)
    generalize dependent A.
    generalize dependent x.
    induction δ as [δ IHδ] using lt_wf_ind => x Hk A.
    (* induction on nonterminal *)
    have Hwf : wf (flip (succ G)) by apply acyclic_succ_flip_wf.
    induction A as [A IHA] using (well_founded_induction Hwf).
    (* rewrite definition *)
    rewrite HΦ; [|done..].
    rewrite check_derive_equation big_or_true Exists_exists.
    split.
    - (* -> *)
      intros [α [Hp Hα]]. exists ⟨α, Hp⟩.
      case_match => //.
      3: destruct Hα as [Hα|[Hα|Hα]].
      + destruct Hα as [-> ?]. repeat case_match => //.
        apply bool_decide_eq_true. naive_solver.
      + destruct Hα as [? ?].
        apply andb_true_iff. split => //.
        clear IHδ. apply IHA => //. eapply succ_unary; eauto.
      + destruct Hα as [Hn ?].
        apply orb_true_iff; left. apply orb_true_iff; left.
        apply when_true. exists Hn.
        clear IHδ. apply IHA => //. eapply succ_right; eauto.
      + destruct Hα as [Hn ?].
        apply orb_true_iff; left. apply orb_true_iff; right.
        apply when_true. exists Hn.
        clear IHδ. apply IHA => //. eapply succ_left; eauto.
      + destruct Hα as [δ' [? [? [? ?]]]].
        apply orb_true_iff; right.
        apply big_or_true.
        have Hpar : (decode m x δ', decode m (x + δ') (δ - δ')) ∈ nonempty_partition (decode m x δ).
        { eapply nonempty_partition_spec; eauto.
          split. rewrite decode_merge. f_equal. lia.
          split. all: apply list_nonempty_length.
          all: rewrite decode_length; lia. }
        exists ⟨(decode m x δ', decode m (x + δ') (δ - δ')), Hpar⟩.
        apply andb_true_iff. split.
        apply andb_true_iff. split => //.
        all: clear IHA; apply IHδ; [lia..|done].
      - (* <- *)
        intros [[α Hp] Hα]. exists α. split; first by apply Hp.
        case_match.
        4: apply orb_true_iff in Hα as [Hα|Hα]; first apply orb_true_iff in Hα as [Hα|Hα].
        + apply bool_decide_eq_true in Hα.
          have ? : decode m x δ ≠ [].
          { apply list_nonempty_length. rewrite decode_length. lia. }
          contradiction.
        + repeat case_match => //.
          apply bool_decide_eq_true in Hα.
          have ? : δ = 1.
          { have Hl : length (decode m x δ) = 1 by rewrite Heqs.
            by rewrite decode_length in Hl. }
          subst. split => //. naive_solver.
        + apply andb_true_iff in Hα as [? ?]. split => //.
          clear IHδ. apply IHA => //. eapply succ_unary; eauto.
        + apply when_true in Hα as [? ?]. left. split => //.
          clear IHδ. apply IHA => //. eapply succ_right; eauto.
        + apply when_true in Hα as [? ?]. right. left. split => //.
          clear IHδ. apply IHA => //. eapply succ_left; eauto.
        + apply big_or_true in Hα as [[[wl wr] Hw] Hα].
          apply andb_true_iff in Hα as [Hα ?].
          apply andb_true_iff in Hα as [? ?].
          right. right.
          eapply nonempty_partition_spec in Hw as [Hw [? ?]]; eauto.
          exists (length wl).
          have ? : length (decode m x δ) = δ by rewrite decode_length.
          have ? : length (decode m x δ) = length wl + length wr
            by rewrite Hw app_length.
          have ? : 0 < length wl by apply list_nonempty_length.
          have ? : 0 < length wr by apply list_nonempty_length.
          have Hw' : decode m x δ = decode m x (length wl) ++
            decode m (x + length wl) (δ - length wl).
            by rewrite decode_merge; f_equal; lia.
          have [Hwl Hwr] : decode m x (length wl) = wl ∧
                           decode m (x + length wl) (δ - length wl) = wr.
          { rewrite Hw in Hw'. apply app_inj_1 => //. by rewrite decode_length.  }
          rewrite Hwl Hwr.
          split; first lia. repeat split => //.
          1,2: clear IHA; apply IHδ; [lia..|].
          by rewrite Hwl. by rewrite Hwr.
    (* TODO: why this is shelved? *)
    Unshelve. done.
  Qed.

End encoding.