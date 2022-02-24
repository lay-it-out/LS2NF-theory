From stdpp Require Import prelude sorting finite.
From Coq Require Import ssreflect.
From LS2NF Require Import grammar util ambiguity acyclic sub_derive slice derivation witness.

Section encoding.

  Context {Σ N : Type} `{!EqDecision Σ} `{!Inhabited Σ} `{!EqDecision N} `{!Finite N}.
  Context (G : grammar Σ N) `{!acyclic G}.

  Open Scope grammar_scope.

  (* sat model *)

  Record model := {
    term : nat → Σ;
    line : nat → nat;
    col : nat → nat;
    line_col i := (line i, col i);
    can_derive : N → nat (* start (inclusive) *) → nat (* length, positive *) → Prop;
    can_reach_from : N → nat (* start (inclusive) *) → nat (* length, positive *) → Prop;
    ε_can_reach_from : N → Prop;
  }.

  (* decode *)

  Definition decode m k : sentence Σ :=
    (λ i, term m i @ (line m i, col m i)) <$> (index_range k).

  Lemma decode_length m k :
    length (decode m k) = k.
  Proof.
    by rewrite fmap_length index_range_length.
  Qed.

  Lemma decode_lookup m k i :
    i < k → (decode m k) !! i = Some (term m i @ (line m i, col m i)).
  Proof.
    intros. rewrite list_lookup_fmap index_range_lookup //.
  Qed.

  Definition encode S (w : sentence Σ) : model := {|
    term i :=
      match w !! i with
      | Some (a @ _) => a
      | None => inhabitant
      end;
    line i :=
      match w !! i with
      | Some (_ @ (x, _)) => x
      | None => 0
      end;
    col i :=
      match w !! i with
      | Some (_ @ (_, y)) => y
      | None => 0
      end;
    can_derive A x δ := (G ⊨ A => slice w x δ);
    can_reach_from A x δ := (reachable G (S, w) (A, slice w x δ));
    ε_can_reach_from A := (reachable G (S, w) (A, []));
  |}.

  Lemma decode_encode S w :
    decode (encode S w) (length w) = w.
  Proof.
    apply list_eq_same_length with (n := length w) => //.
    { by rewrite decode_length. }
    intros i x y ?. rewrite decode_lookup //=. repeat case_match.
    all: intros ?; match goal with
    | H : ?x = _ |- ?x = _ → _ => rewrite H
    end => //.
    congruence.
  Qed.

  Implicit Type w : sentence Σ.
  Implicit Type x δ : nat.

  (* this is our ground truth: ill-formed sentences are not considered *)
  Axiom sentence_well_formed : ∀ w, well_formed w.

  Lemma well_formed_no_dup w : NoDup w.
  Proof.
    have := (sentence_well_formed w).
    induction w as [|a w IHw] => Hwf; constructor.
    - apply Sorted_extends in Hwf. 2: apply pos_token_lt_trans.
      rewrite ->Forall_forall in Hwf.
      intros Hin. specialize (Hwf _ Hin). destruct a as [? [x y]].
      unfold pos_token_lt in Hwf. simpl in Hwf. lia.
    - invert Hwf. eauto.
  Qed.

  Hint Resolve well_formed_no_dup : core.

  (* formula: a predicate over a bounded model *)

  Definition formula : Type := nat → model → Prop.

  (* encoding predicate *)

  Variable Φ_app₁ : (unary_predicate Σ) → nat → nat → formula.
  Variable Φ_app₁_spec : ∀ φ x δ k m,
    Φ_app₁ φ x δ k m ↔ app₁ φ (slice (decode m k) x δ) = true.

  Variable Φ_app₂ : (binary_predicate Σ) → nat → nat → nat → nat → formula.
  Variable Φ_app₂_spec : ∀ φ x1 δ1 x2 δ2 k m,
    Φ_app₂ φ x1 δ1 x2 δ2 k m ↔
      app₂ φ (slice (decode m k) x1 δ1) (slice (decode m k) x2 δ2) = true.

  (* encoding derivation *)

  Definition Φ_derive : formula := λ k m,
    ∀ A x δ, 0 < δ (* nonempty *) → x + δ ≤ k →
      can_derive m A x δ ↔ (
        False ∨
        (∃ a, A ↦ atom a ∈ G ∧ δ = 1 ∧ term m x = a) ∨
        (∃ B φ, A ↦ unary B φ ∈ G ∧ Φ_app₁ φ x δ k m ∧ can_derive m B x δ) ∨
        (∃ Bl Br φ, A ↦ binary Bl Br φ ∈ G ∧ (
          (G ⊨ Bl => [] ∧ can_derive m Br x δ) ∨
          (G ⊨ Br => [] ∧ can_derive m Bl x δ) ∨
          (∃ δ', 0 < δ' < δ ∧
            can_derive m Bl x δ' ∧ can_derive m Br (x + δ') (δ - δ') ∧
            Φ_app₂ φ x δ' (x + δ') (δ - δ') k m)
        ))
      ).

  Lemma Φ_derive_sat X w :
    Φ_derive (length w) (encode X w).
  Proof.
    intros A x δ ? ?.
    have Heq : can_derive (encode X w) A x δ ↔ check_derive G A (slice w x δ).
    { rewrite check_derive_spec derivation_spec //. }
    rewrite Heq.
    unfold check_derive. setoid_rewrite derivation_spec.
    simpl can_derive.
    setoid_rewrite Φ_app₁_spec. setoid_rewrite Φ_app₂_spec.
    setoid_rewrite decode_encode.
    repeat apply ZifyClasses.or_morph.
    - rewrite slice_nil_iff; lia.
    - split.
      + intros [a [p [Hw ?]]]. exists a.
        apply slice_singleton_iff in Hw as [-> Hw] => //.
        repeat split => //=. by rewrite Hw.
      + intros [a [? [? Hw]]].
        have [? Hx] : is_Some (w !! x) by apply lookup_lt_is_Some; lia.
        simpl in Hw. rewrite Hx in Hw. case_match; subst.
        exists a. eexists. rewrite slice_singleton_iff //.
        repeat split; eauto.
    - done.
    - split.
      + intros [Bl [Br [φ [? [w1 [w2 [Hw [Hφ [HBl HBr]]]]]]]]].
        have Hl : length (w1 ++ w2) = δ.
        { apply (f_equal length) in Hw. by rewrite slice_length in Hw. }
        exists Bl, Br, φ. split; first done.
        destruct w1 as [|tk1 w1]; last destruct w2.
        * left. rewrite app_nil_l in Hw. by rewrite Hw.
        * right; left. rewrite app_nil_r in Hw. by rewrite Hw.
        * right; right. apply slice_app_inv_NoDup in Hw as [Hw1 Hw2] => //.
          rewrite app_length !cons_length in Hl.
          exists (length (tk1 :: w1)). rewrite -Hw1 -Hw2.
          repeat split => //. all: rewrite cons_length; lia.
      + intros [Bl [Br [φ [? [Hd|[Hd|Hd]]]]]].
        * destruct Hd as [? ?].
          exists Bl, Br, φ. split; first done.
          exists [], (slice w x δ). rewrite app_nil_l.
          repeat split => //. destruct φ as [φ Hφ]; apply Hφ; by left.
        * destruct Hd as [? ?].
          exists Bl, Br, φ. split; first done.
          exists (slice w x δ), []. rewrite app_nil_r.
          repeat split => //. destruct φ as [φ Hφ]; apply Hφ; by right.
        * destruct Hd as [δ' [? [? [? ?]]]].
          exists Bl, Br, φ. split; first done.
          exists (slice w x δ'), (slice w (x + δ') (δ - δ')).
          rewrite slice_app_1. have -> : δ' + (δ - δ') = δ by lia.
          repeat split => //.
  Qed.

  Lemma list_nonempty_length {A} (l : list A) :
    l ≠ [] ↔ 0 < length l.
  Proof.
    have -> : 0 < length l ↔ 0 ≠ length l by split; [apply lt_0_neq | apply neq_0_lt].
    apply not_iff_compat.
    have ? := length_zero_iff_nil.
    naive_solver.
  Qed.
  
  Lemma Φ_derive_spec k m :
    Φ_derive k m →
    ∀ A x δ, 0 < δ → x + δ ≤ k →
      can_derive m A x δ ↔ G ⊨ A => slice (decode m k) x δ.
  Proof.
    intros HΦ A x δ ? ?.
    (* induction on range length *)
    generalize dependent A.
    generalize dependent x.
    induction δ as [δ IHδ] using lt_wf_ind => x Hk A.
    (* induction on nonterminal *)
    have Hwf : wf (flip (succ G)) by apply acyclic_prec_wf.
    induction A as [A IHA] using (well_founded_induction Hwf).
    (* rewrite definition *)
    rewrite HΦ; [|done..]. setoid_rewrite Φ_app₁_spec. setoid_rewrite Φ_app₂_spec.
    rewrite -derivation_spec -check_derive_spec /check_derive. setoid_rewrite derivation_spec.
    repeat apply ZifyClasses.or_morph.
    - rewrite slice_nil_iff ?decode_length; lia.
    - split.
      + intros [a [? [-> ?]]]. exists a, (line m x, col m x).
        rewrite slice_singleton_iff ?decode_length //.
        rewrite decode_lookup; [lia|].
        naive_solver.
      + intros [a [p [Hw ?]]]. exists a.
        apply slice_singleton_iff in Hw as [-> Hw]; last by rewrite decode_length.
        rewrite decode_lookup in Hw; [lia|].
        naive_solver.
    - split.
      + intros [B [φ [? [? ?]]]]. exists B, φ.
        repeat split => //. apply IHA => //. eapply succ_unary; eauto.
      + intros [B [φ [? [? ?]]]]. exists B, φ.
        repeat split => //. apply IHA => //. eapply succ_unary; eauto.
    - split.
      + intros [Bl [Br [φ [? [Hd|[Hd|Hd]]]]]].
        * destruct Hd as [? ?].
          exists Bl, Br, φ. split; first done.
          exists []. eexists. rewrite app_nil_l.
          repeat split => //; first by destruct φ as [φ Hφ]; apply Hφ; by left.
          apply IHA => //. eapply succ_right; eauto.
        * destruct Hd as [? ?].
          exists Bl, Br, φ. split; first done.
          eexists. exists []. rewrite app_nil_r.
          repeat split => //; first by destruct φ as [φ Hφ]; apply Hφ; by right.
          apply IHA => //. eapply succ_left; eauto.
        * destruct Hd as [δ' [? [? [? ?]]]].
          exists Bl, Br, φ. split; first done.
          do 2 eexists. repeat split; eauto.
          { rewrite -slice_split; [lia | done]. }
          all: apply IHδ => //; lia.
      + intros [Bl [Br [φ [? [w1 [w2 [Hw [Hφ [HBl HBr]]]]]]]]].
        have Hl : length (w1 ++ w2) = δ.
        { apply (f_equal length) in Hw. rewrite slice_length in Hw; [rewrite decode_length; lia | done]. }
        exists Bl, Br, φ. split; first done.
        destruct w1 as [|tk1 w1]; last destruct w2.
        * left. rewrite app_nil_l in Hw. split => //. 
          apply IHA => //. eapply succ_right; eauto. by rewrite Hw.
        * right; left. rewrite app_nil_r in Hw. split => //.
          apply IHA => //. eapply succ_left; eauto. by rewrite Hw.
        * right; right. apply slice_app_inv_NoDup in Hw as [Hw1 Hw2] => //.
          2: rewrite decode_length //.
          rewrite Hw1 in HBl, Hφ. rewrite Hw2 in HBr, Hφ.
          rewrite app_length !cons_length in Hl.
          exists (length (tk1 :: w1)). repeat split => //.
          3-4: apply IHδ => //.
          all: rewrite cons_length; lia.
  Qed.

  (* encoding reachable from (S, [0..k]) *)
  Definition Φ_reach_nonempty S : formula := λ k m,
    ∀ B x δ, 0 < δ → x + δ ≤ k →
      can_reach_from m B x δ ↔ (
        (B = S ∧ x = 0 ∧ δ = k) ∨
        (∃ A φ, A ↦ unary B φ ∈ G ∧ can_reach_from m A x δ ∧ Φ_app₁ φ x δ k m) ∨
        (∃ A B' φ δ', x + δ + δ' ≤ k ∧ A ↦ binary B B' φ ∈ G ∧ can_reach_from m A x (δ + δ') ∧
          (if bool_decide (δ' = 0) then G ⊨ B' => [] else can_derive m B' (x + δ) δ') ∧
          Φ_app₂ φ x δ (x + δ) δ' k m) ∨
        (∃ A B' φ δ', δ' ≤ x ∧ A ↦ binary B' B φ ∈ G ∧ can_reach_from m A (x - δ') (δ' + δ) ∧
          (if bool_decide (δ' = 0) then G ⊨ B' => [] else can_derive m B' (x - δ') δ') ∧
          Φ_app₂ φ (x - δ') δ' x δ k m)
      ).

  Definition Φ_reach_empty S : formula := λ k m,
    ∀ B, ε_can_reach_from m B ↔ (
      (B = S ∧ k = 0) ∨
      (∃ A φ, A ↦ unary B φ ∈ G ∧ ε_can_reach_from m A) ∨
      (∃ A B' φ, A ↦ binary B B' φ ∈ G ∧ (
        (ε_can_reach_from m A ∧ G ⊨ B' => []) ∨
        (∃ x δ, 0 < δ ∧ x + δ ≤ k ∧
          can_reach_from m A x δ ∧ can_derive m B' x δ))) ∨
      (∃ A B' φ, A ↦ binary B' B φ ∈ G ∧ (
        (ε_can_reach_from m A ∧ G ⊨ B' => []) ∨
        (∃ x δ, 0 < δ ∧ x + δ ≤ k ∧
          can_reach_from m A x δ ∧ can_derive m B' x δ)))
    ).

  Definition Φ_reach S : formula := λ k m,
    Φ_reach_nonempty S k m ∧ Φ_reach_empty S k m.

  Lemma Φ_reach_nonempty_sat X w k :
    length w = k →
    Φ_reach_nonempty X k (encode X w).
  Proof.
    intros <- B x δ ? ?.
    have Heq : can_reach_from (encode X w) B x δ ↔ check_reachable_from G (X, w) (B, slice w x δ).
    { rewrite check_reachable_from_spec reachable_from_spec //. }
    rewrite Heq /=.
    setoid_rewrite reachable_from_spec.
    setoid_rewrite Φ_app₁_spec. setoid_rewrite Φ_app₂_spec.
    setoid_rewrite decode_encode.
    repeat apply ZifyClasses.or_morph.
    - rewrite slice_full_iff //. apply list_nonempty_length; lia.
    - done.
    - split.
      + intros [A [B' [φ [wr [? [Hr [? ?]]]]]]].
        exists A, B', φ, (length wr).
        destruct wr as [|tk l].
        * rewrite /= slice_nil !Nat.add_0_r.
          rewrite app_nil_r in Hr.
          repeat split => //.
        * case_bool_decide => //. 
          have Hsub : sublist (slice w x δ ++ tk :: l) w by eapply reachable_sublist; eauto.
          apply sublist_app_slice_NoDup in Hsub as [x' [Hlen [Hx' Hl]]];
            [| eauto | rewrite slice_length; lia | lia].
          rewrite slice_length in Hlen => //.
          apply slice_eq_inv_NoDup in Hx' as [? Hδ] => //; [|rewrite slice_length; lia..].
          subst. rewrite Hδ in Hl. rewrite -slice_app_1 -Hl.
          repeat split => //.
      + intros [A [B' [φ [δ' [? [? [Hr [Hd Hφ]]]]]]]].
        exists A, B', φ, (slice w (x + δ) δ').
        rewrite slice_app_1.
        repeat split => //.
        case_bool_decide; [by subst | done].
    - split.
      + intros [A [B' [φ [wl [? [Hr [? ?]]]]]]].
        exists A, B', φ, (length wl).
        destruct wl as [|tk l].
        * rewrite /= slice_nil !Nat.sub_0_r.
          rewrite app_nil_l in Hr.
          repeat split => //. lia.
        * case_bool_decide => //. 
          have Hsub : sublist ((tk :: l) ++ slice w x δ) w by eapply reachable_sublist; eauto.
          apply sublist_app_slice_NoDup in Hsub as [x' [Hlen [Hx' Hl]]];
            [| eauto | rewrite cons_length; lia | rewrite slice_length; lia].
          rewrite slice_length in Hlen => //. rewrite slice_length in Hl => //.
          apply slice_eq_inv_NoDup in Hl as [? Hδ] => //; [|rewrite slice_length; lia..].
          subst. rewrite Nat.add_sub -slice_app_1 -Hx'.
          repeat split => //. lia.
      + intros [A [B' [φ [δ' [? [? [Hr [Hd Hφ]]]]]]]].
        exists A, B', φ, (slice w (x - δ') δ').
        rewrite slice_app_2; [lia|].
        repeat split => //.
        case_bool_decide; [by subst | done].
  Qed.

  Lemma apply_unary_nil (φ : unary_predicate Σ) :
    app₁ φ [] = true.
  Proof. by destruct φ. Qed.

  Lemma apply_binary_nil_l (φ : binary_predicate Σ) w :
    app₂ φ [] w = true.
  Proof. destruct φ; naive_solver. Qed.

  Lemma apply_binary_nil_r (φ : binary_predicate Σ) w :
    app₂ φ w [] = true.
  Proof. destruct φ; naive_solver. Qed.

  Lemma Φ_reach_empty_sat k X w :
    length w = k →
    Φ_reach_empty X k (encode X w).
  Proof.
    intros <- B.
    have Heq : ε_can_reach_from (encode X w) B ↔ check_reachable_from G (X, w) (B, []).
    { rewrite check_reachable_from_spec reachable_from_spec //. }
    rewrite Heq /=.
    setoid_rewrite reachable_from_spec.
    repeat apply ZifyClasses.or_morph.
    - rewrite length_zero_iff_nil. naive_solver.
    - setoid_rewrite apply_unary_nil. naive_solver.
    - setoid_rewrite apply_binary_nil_l. split.
      + intros [A [B' [φ [w' [? [Hr [? ?]]]]]]].
        exists A, B', φ. split; first done.
        destruct w' as [|t w']; [by left | right].
        have Hsub : sublist (t :: w') w by eapply reachable_sublist; eauto.
        apply sublist_slice in Hsub as [a [? Hw]].
        exists a, (length (t :: w')).
        rewrite -Hw. repeat split => //. rewrite cons_length; lia.
      + intros [A [B' [φ [? [Hr|Hr]]]]].
        * destruct Hr as [? ?].
          exists A, B', φ, [].
          repeat split => //.
        * destruct Hr as [x [δ [? [? [? ?]]]]].
          exists A, B', φ, (slice w x δ).
          repeat split => //.
    - setoid_rewrite apply_binary_nil_r.
      setoid_rewrite app_nil_r. split.
      + intros [A [B' [φ [w' [? [Hr [? ?]]]]]]].
        exists A, B', φ. split; first done.
        destruct w' as [|t w']; [by left | right].
        have Hsub : sublist (t :: w') w by eapply reachable_sublist; eauto.
        apply sublist_slice in Hsub as [a [? Hw]].
        exists a, (length (t :: w')).
        rewrite -Hw. repeat split => //. rewrite cons_length; lia.
      + intros [A [B' [φ [? [Hr|Hr]]]]].
        * destruct Hr as [? ?].
          exists A, B', φ, [].
          repeat split => //.
        * destruct Hr as [x [δ [? [? [? ?]]]]].
          exists A, B', φ, (slice w x δ).
          repeat split => //.
  Qed.

  Lemma Φ_reach_sat k X w :
    length w = k →
    Φ_reach X k (encode X w).
  Proof.
    intros <-. split; by [apply Φ_reach_nonempty_sat | apply Φ_reach_empty_sat].
  Qed.

  Lemma Φ_reach_nonempty_spec k S m :
    Φ_derive k m →
    Φ_reach_nonempty S k m →
    ∀ B x δ, 0 < δ → x + δ ≤ k →
      can_reach_from m B x δ → (* only this direction is needed *)
      reachable G (S, decode m k) (B, slice (decode m k) x δ).
  Proof.
    intros HΦ' HΦ B x δ ? ? ?. rewrite -reachable_from_spec.
    (* induction on range length *)
    generalize dependent B.
    generalize dependent x.
    induction δ as [δ IHδ] using (induction_ltof1 _ (λ δ, k - δ)) => x Hk B.
    unfold ltof in IHδ.
    (* induction on nonterminal *)
    have Hwf : wf (succ G) by apply acyclic_succ_wf.
    induction B as [B IHB] using (well_founded_induction Hwf).
    rewrite HΦ //.
    setoid_rewrite Φ_app₁_spec. setoid_rewrite Φ_app₂_spec.
    intros [Hr|[Hr|[Hr|Hr]]].
    - destruct Hr as [-> [-> ->]].
      rewrite slice_full ?decode_length //.
      constructor.
    - destruct Hr as [A [φ [? [? ?]]]].
      eapply reachable_from_unary; eauto.
      apply IHB => //. eapply succ_unary; eauto.
    - destruct Hr as [A [B' [φ [δ' [? [? [? [? ?]]]]]]]].
      case_bool_decide; subst.
      * eapply reachable_from_left; eauto.
        rewrite app_nil_r. apply IHB.
        { eapply succ_left; eauto. }
        have -> : δ = δ + 0 by lia. done.
      * eapply reachable_from_left; eauto.
        rewrite slice_app_1. apply IHδ => //; lia.
        { eapply Φ_derive_spec; eauto; lia. }
    - destruct Hr as [A [B' [φ [δ' [? [? [Hr [? ?]]]]]]]].
      case_bool_decide; subst; eapply reachable_from_right; eauto.
      * rewrite Nat.sub_0_r Nat.add_0_l in Hr. rewrite app_nil_l.
        apply IHB => //. eapply succ_right; eauto.
      * rewrite slice_app_2 //. apply IHδ => //; lia.
      * eapply Φ_derive_spec; eauto; lia.
  Qed.

  Lemma Φ_reach_empty_spec S k m :
    Φ_derive k m →
    Φ_reach_nonempty S k m →
    Φ_reach_empty S k m →
    ∀ B,
      ε_can_reach_from m B → (* only this direction is needed *)
      reachable G (S, decode m k) (B, []).
  Proof.
    intros ? ? HΦ B. rewrite -reachable_from_spec.
    (* induction on nonterminal *)
    have Hwf : wf (succ G) by apply acyclic_succ_wf.
    induction B as [B IHB] using (well_founded_induction Hwf).
    rewrite HΦ //. intros [Hr|[Hr|[Hr|Hr]]].
      + destruct Hr as [<- ->]. constructor.
      + destruct Hr as [A [φ [Hp ?]]].
        eapply reachable_from_unary; [apply Hp | | apply apply_unary_nil].
        apply IHB => //. eapply succ_unary; eauto.
      + destruct Hr as [A [B' [φ [Hp [Hr|Hr]]]]].
        * destruct Hr as [? ?].
          eapply reachable_from_left; [apply Hp | | eauto | apply apply_binary_nil_l].
          rewrite app_nil_l. apply IHB => //. eapply succ_left; eauto.
        * destruct Hr as [x [δ [? [? [Hr Hd]]]]].
          eapply Φ_derive_spec in Hd; eauto.
          eapply reachable_from_left; [apply Hp | | eauto | apply apply_binary_nil_l].
          rewrite app_nil_l. apply reachable_from_spec, Φ_reach_nonempty_spec; eauto.
      + destruct Hr as [A [B' [φ [Hp [Hr|Hr]]]]].
        * destruct Hr as [? ?].
          eapply reachable_from_right; [apply Hp | | eauto | apply apply_binary_nil_r].
          rewrite app_nil_r. apply IHB => //. eapply succ_right; eauto.
        * destruct Hr as [x [δ [? [? [Hr Hd]]]]].
          eapply Φ_derive_spec in Hd; eauto.
          eapply reachable_from_right; [apply Hp | | eauto | apply apply_binary_nil_r].
          rewrite app_nil_r. apply reachable_from_spec, Φ_reach_nonempty_spec; eauto.
  Qed.

  (* encoding derivations using different productions *)

  Inductive using_clause : Type :=
  | using_ε : using_clause
  | using_atom : Σ → using_clause
  | using_unary : N → unary_predicate Σ → using_clause
  | using_binary : N → N → binary_predicate Σ → nat (* length of first part *) → using_clause
  .

  Definition usable_clauses A δ : list using_clause :=
    clauses G A ≫= (λ α, match α with
    | ε => [using_ε]
    | atom a => [using_atom a]
    | unary B φ => [using_unary B φ]
    | binary Bl Br φ => (λ δ', using_binary Bl Br φ δ') <$> (index_range δ ++ [δ])
    end).

  Lemma elem_of_usable_clauses ψ A δ :
    ψ ∈ usable_clauses A δ ↔ match ψ with
    | using_ε => A ↦ ε ∈ G
    | using_atom a => A ↦ atom a ∈ G
    | using_unary B φ => A ↦ unary B φ ∈ G
    | using_binary Bl Br φ δ' => A ↦ binary Bl Br φ ∈ G ∧ δ' ≤ δ
    end.
  Proof.
    rewrite /usable_clauses elem_of_list_bind. split.
    - (* -> *)
      intros [α [Hin ?]]. repeat case_match => //.
      all: repeat match goal with
      | [H : _ ∈ [_] |- _ ] => apply elem_of_list_singleton in H; invert H
      | [H : _ ∈ _ <$> _ |- _ ] => apply elem_of_list_fmap in H as [x [H Hx]]; invert H
      end => //.
      split => //. apply elem_of_app in Hx as [|Hx].
      * suff : x < δ by lia. by apply index_range_elem_of.
      * suff : x = δ by lia. by apply elem_of_list_singleton in Hx.
    - (* <- *)
      destruct ψ as [| a | B φ | Bl Br φ δ'] => Hp.
      * exists ε. split => //. by apply elem_of_list_singleton.
      * exists (atom a). split => //. by apply elem_of_list_singleton.
      * exists (unary B φ). split => //. by apply elem_of_list_singleton.
      * exists (binary Bl Br φ). destruct Hp as [? Hδ']. split => //. apply elem_of_list_fmap.
        exists δ'. split => //. apply Nat.le_lteq in Hδ' as [?|?]; apply elem_of_app; by
          [left; apply index_range_elem_of | right; apply elem_of_list_singleton].
  Qed.
  
  Definition Φ_using_derive ψ x δ : formula :=
    match ψ with
    | using_ε => λ k m, δ = 0
    | using_atom a => λ k m, δ = 1 ∧ term m x = a
    | using_unary B φ => λ k m,
      if bool_decide (δ = 0) then G ⊨ B => []
      else Φ_app₁ φ x δ k m ∧ can_derive m B x δ
    | using_binary Bl Br φ δ' => λ k m,
      (if bool_decide (δ' = 0) then G ⊨ Bl => [] else can_derive m Bl x δ') ∧
      (if bool_decide (δ - δ' = 0) then G ⊨ Br => [] else can_derive m Br (x + δ') (δ - δ')) ∧
      Φ_app₂ φ x δ' (x + δ') (δ - δ') k m
    end.

  Lemma Φ_using_derive_witness k m x δ A ψ :
    Φ_derive k m →
    x + δ ≤ k →
    ψ ∈ usable_clauses A δ →
    Φ_using_derive ψ x δ k m ↔ match ψ with
    | using_ε => δ = 0 ∧ ε_tree A ▷ A ={G}=> slice (decode m k) x δ
    | using_atom a => δ = 1 ∧ a = term m x ∧ let p := (line m x, col m x) in
      (token_tree A (a @ p)) ▷ A ={G}=> slice (decode m k) x δ
    | using_unary B _ => ∃ t, root t = B ∧ (unary_tree A t) ▷ A ={G}=> slice (decode m k) x δ
    | using_binary Bl Br _ δ' => ∃ t1 t2, root t1 = Bl ∧ root t2 = Br ∧
      word t1 = slice (decode m k) x δ' ∧ (binary_tree A t1 t2) ▷ A ={G}=> slice (decode m k) x δ
    end.
  Proof.
    intros ? ? Hψ. destruct ψ as [| a | B φ | Bl Br φ δ'] => /=.
    all: apply elem_of_usable_clauses in Hψ.
    - split; last naive_solver.
      intros ->. split; first done. by apply witness_ε.
    - split; last naive_solver.
      intros [-> Hx]. split; first done.
      erewrite slice_singleton; last by rewrite decode_lookup; [lia|eauto].
      rewrite Hx. split; first done. by apply witness_atom.
    - unfold derive. case_bool_decide.
      + subst. rewrite slice_nil. split.
        * intros [t [? [? ?]]]. subst. exists t.
          rewrite witness_unary; eauto. repeat split => //. apply apply_unary_nil.
        * intros [t [? Ht]]. subst. eapply witness_unary in Ht; eauto. naive_solver.
      + rewrite Φ_app₁_spec.
        rewrite Φ_derive_spec; eauto; [|lia]. unfold derive.
        split.
        * intros [? [t [? [? ?]]]]. subst. exists t.
          rewrite witness_unary; eauto. repeat split => //.
        * intros [t [? Ht]]. subst. eapply witness_unary in Ht; eauto. naive_solver.
    - destruct Hψ as [Hψ ?]. unfold derive. rewrite Φ_app₂_spec. repeat case_bool_decide.
      Ltac finish := split;
        [ intros [[t1 [? [Hw1 ?]]] [[t2 [? [? ?]]] ?]]; subst; exists t1, t2;
          rewrite -{2}Hw1 witness_binary ?Hw1; eauto; repeat split => //
        | intros [t1 [t2 [? [? [Hw1 Ht]]]]]; subst;
          rewrite -{1}Hw1 in Ht; eapply witness_binary in Ht; eauto; rewrite Hw1 in Ht; naive_solver 
        ].
      + have -> : δ = 0 by lia.
        have -> : slice (decode m k) x 0 = [] ++ [] by rewrite slice_nil.
        have -> : δ' = 0 by lia. rewrite slice_nil.
        finish.
      + have -> : slice (decode m k) x δ = [] ++ slice (decode m k) x δ by rewrite app_nil_l.
        subst. rewrite Nat.add_0_r Nat.sub_0_r slice_nil.
        rewrite Φ_derive_spec; eauto; [|lia]. unfold derive.
        finish.
      + have -> : slice (decode m k) x δ = slice (decode m k) x δ ++ [] by rewrite app_nil_r.
        have -> : δ' = δ by lia. rewrite Nat.sub_diag slice_nil.
        rewrite Φ_derive_spec; eauto; [|lia]. unfold derive.
        finish.
      + have -> : slice (decode m k) x δ = slice (decode m k) x δ' ++ slice (decode m k) (x + δ') (δ - δ')
          by rewrite -slice_split.
        rewrite !Φ_derive_spec; eauto; [|lia..]. unfold derive.
        finish.
  Qed.

  Definition Φ_multi_usable (A : N) (x δ : nat) : formula := λ k m,
    ∃ ψ1, ψ1 ∈ usable_clauses A δ ∧
      ∃ ψ2, ψ2 ∈ usable_clauses A δ ∧
        ψ1 ≠ ψ2 ∧ Φ_using_derive ψ1 x δ k m ∧ Φ_using_derive ψ2 x δ k m.

  Lemma app_length_le_l {A} (l1 l2 l : list A) :
    l1 ++ l2 = l →
    length l1 ≤ length l.
  Proof.
    intros Hl. apply (f_equal length) in Hl. rewrite app_length in Hl. lia.
  Qed.

  Local Lemma wrap_with_id (P : Prop) :
    P ↔ id P.
  Proof. done. Qed.

  Local Ltac wrap H := apply ->wrap_with_id in H.

  Local Ltac congruence_by H :=
    match goal with
    | H1 : ?x = ?z1, H2 : ?y = ?z2, H : ?x = ?y |- _ =>
      rewrite H1 in H; rewrite H2 in H
    end.

  Lemma Φ_multi_usable_spec k m x δ A :
    Φ_derive k m →
    x + δ ≤ k →
    Φ_multi_usable A x δ k m ↔ ∃ t1, t1 ▷ A ={G}=> slice (decode m k) x δ ∧
      ∃ t2, t2 ▷ A ={G}=> slice (decode m k) x δ ∧ ¬ similar t1 t2.
  Proof.
    intros ? ?. split.
    - (* -> *)
      intros [ψ1 [Hψ1 [ψ2 [Hψ2 [Hne [HΦ1 HΦ2]]]]]].
      eapply Φ_using_derive_witness in HΦ1; eauto.
      eapply Φ_using_derive_witness in HΦ2; eauto.
      repeat case_match.
      all: apply elem_of_usable_clauses in Hψ1, Hψ2.
      all: repeat match goal with
      | [ H : _ ∧ _ |- _ ] => destruct H as [H ?]
      | [ H : ∃ _, _ |- _ ] => destruct H as [? H]
      end.
      all: simpl in *; try congruence.
      all: repeat match goal with
      | [ H : ?t ▷ ?A ={?G}=> ?w |- ∃ t, t ▷ ?A ={?G}=> ?w ∧ _ ] =>
        exists t; split; [by apply H|]; clear H
      end => //=.
      * intros Heq. subst. rewrite Heq in Hψ2.
        eapply unary_clause_predicate_unique in Hψ1; [|exact Hψ2].
        subst. congruence.
      * intros [Heq1 [Heq2 Heqw]]. subst. rewrite Heq1 Heq2 in Hψ2.
        eapply binary_clause_predicate_unique in Hψ1; [|exact Hψ2].
        subst. congruence_by Heqw.
        apply slice_eq_inv in Heqw. 2-3: rewrite decode_length; lia.
        congruence.
    - (* <- *)
      intros [t1 [[? [? Ht1]] [t2 [[? [? Ht2]] ?]]]].
      destruct t1 as [?|??|??|? t11 t12]; destruct t2 as [?|??|??|? t21 t22].
      all: simpl in *; try done; try congruence.
      all: invert Ht1.
      all: invert Ht2.
      all: unfold Φ_multi_usable.
      all: repeat match goal with
      | [ H : ?A ↦ ε ∈ _ |- ∃ ψ, ψ ∈ usable_clauses ?A ?δ ∧ _ ] =>
        assert (using_ε ∈ usable_clauses A δ) by (by apply elem_of_usable_clauses);
        eexists; split; [eauto|]; wrap H
      | [ H : ?A ↦ atom ?a ∈ _ |- ∃ ψ, ψ ∈ usable_clauses ?A ?δ ∧ _ ] =>
        assert (using_atom a ∈ usable_clauses A δ) by (by apply elem_of_usable_clauses);
        eexists; split; [eauto|]; wrap H
      | [ H : ?A ↦ unary ?B ?φ ∈ _ |- ∃ ψ, ψ ∈ usable_clauses ?A ?δ ∧ _ ] =>
        assert (using_unary B φ ∈ usable_clauses A δ) by (by apply elem_of_usable_clauses);
        eexists; split; [eauto|]; wrap H
      | [ H : ?A ↦ binary (root ?t1) (root ?t2) ?φ ∈ _ |- ∃ ψ, ψ ∈ usable_clauses ?A ?δ ∧ _ ] =>
        assert (using_binary (root t1) (root t2) φ (length (word t1)) ∈ usable_clauses A δ) by
          (apply elem_of_usable_clauses; split; [done 
            | erewrite <-slice_length; [ eapply app_length_le_l; eauto | by rewrite decode_length ]
          ]);
        eexists; split; [eauto|]; wrap H
      end.
      all: split; first try congruence.
      12: {
        intros Heq. invert Heq.
        have Hw : word t11 ++ word t12 = word t21 ++ word t22 by congruence.
        apply app_inj_1 in Hw => //. naive_solver.
      }
      all: try (split; eapply Φ_using_derive_witness; simpl; eauto).
      all: repeat match goal with
      | [ |- _ ▷ _ ={ _ }=> _ ] =>
        repeat split; simpl; try done; try congruence; econstructor; eauto
      | [ H : [] = slice (decode _ _) _ ?δ |- ?δ = 0 ∧ _ ] =>
        rewrite -H; symmetry in H; apply slice_nil_iff in H; [|by rewrite decode_length]; split; first done
      | [ H : [_] = slice (decode _ _) _ ?δ |- ?δ = 1 ∧ _ = term _ _ ∧ _ ] =>
        rewrite -H; symmetry in H; apply slice_singleton_iff in H; [|by rewrite decode_length];
        let H' := fresh in destruct H as [-> H']; rewrite decode_lookup in H'; [lia|];
        invert H'; do 2 (split; first done)
      | [ |- ∃ t, root t = root ?t' ∧ _ ] =>
        exists t'; split; first done
      | [ |- ∃ t1 t2, root t1 = root ?t1' ∧ root t2 = root ?t2' ∧ _ ] =>
        exists t1', t2'; do 2 (split; first done)
      | [ |- word ?t = slice (decode _ _) _ _ ∧ _ ] =>
        split; first by (eapply slice_app_inv_NoDup; eauto; rewrite decode_length; lia)
      end.
  Qed.

  (* Main theorems *)

  Definition Φ_amb A : formula := λ k m,
    Φ_derive k m ∧ Φ_reach A k m ∧ ∃ H,
     (ε_can_reach_from m H ∧ Φ_multi_usable H 0 0 k m) ∨
     (∃ x δ, 0 < δ ∧ x + δ ≤ k ∧ can_reach_from m H x δ ∧ Φ_multi_usable H x δ k m).

  Theorem Φ_amb_sound A k m :
    Φ_amb A k m → derive_amb G A (decode m k).
  Proof.
    intros [? [[? ?] [X HX]]].
    apply derive_amb_iff_local_amb => //.
    destruct HX as [[? Hm]|[x [δ [? [? [? Hm]]]]]].
    - exists X, []; split; first by apply Φ_reach_empty_spec.
      eapply Φ_multi_usable_spec in Hm; eauto; last lia.
      simpl in Hm. naive_solver.
    - exists X, (slice (decode m k) x δ); split; first by apply Φ_reach_nonempty_spec.
      eapply Φ_multi_usable_spec in Hm; eauto. naive_solver.
  Qed.

  Theorem Φ_amb_complete X k w :
    length w = k → derive_amb G X w → ∃ m, Φ_amb X k m.
  Proof.
    intros <- Hamb.
    apply derive_amb_iff_local_amb in Hamb; eauto.
    destruct Hamb as [C [h [Hr [t1 [t2 [Ht1 [Ht2 Hne]]]]]]].
    exists (encode X w).
    have HΦ : Φ_derive (length w) (encode X w) by apply Φ_derive_sat.
    have HΦ' : Φ_reach X (length w) (encode X w) by apply Φ_reach_sat.
    do 2 (split; first done). exists C.
    destruct h as [|tk h].
    - left. split; first done.
      eapply Φ_multi_usable_spec; eauto; lia.
    - right.
      have Hsub : sublist (tk :: h) w by eapply reachable_sublist; eauto.
      apply sublist_slice in Hsub as [x [? Hh]].
      exists x, (length (tk :: h)).
      simpl can_reach_from. rewrite -Hh. repeat split => //.
      { rewrite cons_length; lia. }
      eapply Φ_multi_usable_spec; eauto; try congruence.
      rewrite decode_encode -Hh; eauto.
  Qed.

End encoding.