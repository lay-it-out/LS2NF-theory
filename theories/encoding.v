From stdpp Require Import prelude.
From Coq Require Import ssreflect.
From ambig Require Import grammar util ambiguity acyclic sub_derive slice derivation witness.

Section encoding.

  Context {Σ N : Type} `{EqDecision Σ} `{Inhabited Σ} `{EqDecision N}.
  Context (G : grammar Σ N) `{acyclic G}.

  (* sat model *)

  Record model := {
    term : nat → Σ;
    line : nat → nat;
    col : nat → nat;
    line_col i := (line i, col i);
    can_derive : N → nat (* start (inclusive) *) → nat (* length, positive *) → bool;
    can_reach_from : N → nat (* start (inclusive) *) → nat (* length, positive *) → bool;
    ε_can_reach_from : N → bool;
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

  (* encode *)

  Global Instance acyclic_derive_dec A w :
    Decision (G ⊨ A ⇒ w).
  Admitted.

  Global Instance acyclic_reachable_dec A w B h :
    Decision (reachable G (A, w) (B, h)).
  Admitted.

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
    can_derive A x δ := bool_decide (G ⊨ A ⇒ slice w x δ);
    can_reach_from A x δ := bool_decide (reachable G (S, w) (A, slice w x δ));
    ε_can_reach_from A := bool_decide (reachable G (S, w) (A, []));
  |}.

  Lemma decode_encode S w :
    decode (encode S w) (length w) = w.
  Proof.
    apply list_eq_same_length with (n := length w) => //.
    1: by rewrite decode_length.
    intros i x y ?. rewrite decode_lookup //=. repeat case_match.
    - inversion 1; subst. intros Hy.
      have Heq : Some (letter @ (n, n0)) = Some y by rewrite -Hy; symmetry.
      by inversion Heq.
    - rewrite Heqo. inversion 2.
  Qed.

  Implicit Type w : sentence Σ.
  Implicit Type x δ : nat.
  Context `{∀ w, NoDup w}.

  (* formula: a predicate over a bounded model *)

  Definition formula : Type := nat → model → Prop.

  (* encoding predicate *)

  Variable Φ_apply₁ : (unary_predicate Σ) → nat → nat → formula.
  Variable Φ_apply₁_spec : ∀ φ x δ k m,
    Φ_apply₁ φ x δ k m ↔ apply₁ φ (slice (decode m k) x δ) = true.

  Variable Φ_apply₂ : (binary_predicate Σ) → nat → nat → nat → nat → formula.
  Variable Φ_apply₂_spec : ∀ φ x1 δ1 x2 δ2 k m,
    Φ_apply₂ φ x1 δ1 x2 δ2 k m ↔
      apply₂ φ (slice (decode m k) x1 δ1) (slice (decode m k) x2 δ2) = true.

  (* encoding derivation *)

  Definition Φ_derive : formula := λ k m,
    ∀ A x δ, 0 < δ (* nonempty *) → x + δ ≤ k →
      can_derive m A x δ = true ↔ (
        False ∨
        (∃ a, A ↦ atom a ∈ G ∧ δ = 1 ∧ term m x = a) ∨
        (∃ B φ, A ↦ unary B φ ∈ G ∧ Φ_apply₁ φ x δ k m ∧ can_derive m B x δ = true) ∨
        (∃ Bl Br φ, A ↦ binary Bl Br φ ∈ G ∧ (
          (G ⊨ Bl ⇒ [] ∧ can_derive m Br x δ = true) ∨
          (G ⊨ Br ⇒ [] ∧ can_derive m Bl x δ = true) ∨
          (∃ δ', 0 < δ' < δ ∧
            can_derive m Bl x δ' = true ∧ can_derive m Br (x + δ') (δ - δ') = true ∧
            Φ_apply₂ φ x δ' (x + δ') (δ - δ') k m)
        ))
      ).

  Lemma Φ_derive_sat X w :
    Φ_derive (length w) (encode X w).
  Proof.
    intros A x δ ? ?.
    rewrite bool_decide_eq_true -derivation_spec -check_derive_spec.
    unfold check_derive. setoid_rewrite derivation_spec.
    simpl can_derive. setoid_rewrite bool_decide_eq_true.
    setoid_rewrite Φ_apply₁_spec. setoid_rewrite Φ_apply₂_spec.
    setoid_rewrite decode_encode.
    repeat apply ZifyClasses.or_morph.
    - rewrite slice_nil_iff; lia.
    - setoid_rewrite slice_singleton_iff. split.
      + intros [a [p [[? Hw] ?]]]. exists a. repeat split => //=. by rewrite Hw.
      + intros [a [? [? Hw]]].
        have [? Hx] : is_Some (w !! x) by apply lookup_lt_is_Some; lia.
        simpl in Hw. rewrite Hx in Hw. case_match; subst.
        exists a. eexists. repeat split; eauto.
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
          rewrite Hw1 in HBl, Hφ. rewrite Hw2 in HBr, Hφ.
          rewrite app_length !cons_length in Hl.
          exists (length (tk1 :: w1)). repeat split => //. all: rewrite cons_length; lia.
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
          rewrite -slice_app. have -> : δ' + (δ - δ') = δ by lia.
          repeat split => //.
  Qed.

  (* Notation "⟨ x , y ⟩" := (existT x y). *)

  Lemma list_nonempty_length {A} (l : list A) :
    l ≠ [] ↔ 0 < length l.
  Admitted.

  (* TODO: since the encoding has a similar shape to the proof rules for G ⊨ A ⇒ w, 
     we can define those proof rules first using `Inductive`, and then a first-order logic
     proposition using disjunction, and show they are equiv to the original definition.

     In this way, it suffices to show two propositions both using disjunction, but one is using
     `can_derive` and the other `_ ⊨ _ ⇒ _`, are equiv.

     This approach will also simplifies the proof for `Φ_derive k (model_slice _ w)`, given that
     all `can_derive` is defined as `bool_decide (_ ⊨ _ ⇒ _)`.
  *)
  Lemma Φ_derive_spec k m :
    Φ_derive k m →
    ∀ A x δ, 0 < δ → x + δ ≤ k →
      can_derive m A x δ = true ↔ G ⊨ A ⇒ slice (decode m k) x δ.
  Proof.
    intros HΦ A x δ ? ?.
    (* induction on range length *)
    generalize dependent A.
    generalize dependent x.
    induction δ as [δ IHδ] using lt_wf_ind => x Hk A.
    (* induction on nonterminal *)
    have Hwf : wf (flip (succ G)) by apply acyclic_succ_flip_wf.
    induction A as [A IHA] using (well_founded_induction Hwf).
    (* rewrite definition *)
    rewrite HΦ; [|done..]. setoid_rewrite Φ_apply₁_spec. setoid_rewrite Φ_apply₂_spec.
    rewrite -derivation_spec -check_derive_spec /check_derive. setoid_rewrite derivation_spec.
    repeat apply ZifyClasses.or_morph.
    - rewrite slice_nil_iff ?decode_length; lia.
    - setoid_rewrite slice_singleton_iff.
      rewrite decode_lookup; first lia.
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
          1: by rewrite -slice_split.
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
          rewrite Hw1 in HBl, Hφ. rewrite Hw2 in HBr, Hφ.
          rewrite app_length !cons_length in Hl.
          exists (length (tk1 :: w1)). repeat split => //.
          3-4: apply IHδ => //.
          all: rewrite cons_length; lia.
  Qed.

  (* encoding reachable from (S, [0..k]) *)
  Definition Φ_reach_nonempty S : formula := λ k m,
    ∀ B x δ, 0 < δ → x + δ ≤ k →
      can_reach_from m B x δ = true ↔ (
        (B = S ∧ x = 0 ∧ δ = k) ∨
        (∃ A φ, A ↦ unary B φ ∈ G ∧ can_reach_from m A x δ = true ∧ Φ_apply₁ φ x δ k m) ∨
        (∃ A B' φ δ', x + δ + δ' ≤ k ∧ A ↦ binary B B' φ ∈ G ∧ can_reach_from m A x (δ + δ') = true ∧
          (if bool_decide (δ' = 0) then G ⊨ B' ⇒ [] else can_derive m B' (x + δ) δ' = true) ∧
          Φ_apply₂ φ x δ (x + δ) δ' k m) ∨
        (∃ A B' φ δ', δ' ≤ x ∧ A ↦ binary B' B φ ∈ G ∧ can_reach_from m A (x - δ') (δ' + δ) = true ∧
          (if bool_decide (δ' = 0) then G ⊨ B' ⇒ [] else can_derive m B' (x - δ') δ' = true) ∧
          Φ_apply₂ φ (x - δ') δ' x δ k m)
      ).

  Definition Φ_reach_empty S : formula := λ k m,
    ∀ B, ε_can_reach_from m B = true ↔ (
      (B = S ∧ k = 0) ∨
      (∃ A φ, A ↦ unary B φ ∈ G ∧ ε_can_reach_from m A = true) ∨
      (∃ A B' φ, A ↦ binary B B' φ ∈ G ∧ (
        (ε_can_reach_from m A = true ∧ G ⊨ B' ⇒ []) ∨
        (∃ x δ, 0 < δ ∧ x + δ ≤ k ∧
          can_reach_from m A x δ = true ∧ can_derive m B' x δ = true))) ∨
      (∃ A B' φ, A ↦ binary B' B φ ∈ G ∧ (
        (ε_can_reach_from m A = true ∧ G ⊨ B' ⇒ []) ∨
        (∃ x δ, 0 < δ ∧ x + δ ≤ k ∧
          can_reach_from m A x δ = true ∧ can_derive m B' x δ = true)))
    ).

  Definition Φ_reach S : formula := λ k m,
    Φ_reach_nonempty S k m ∧ Φ_reach_empty S k m.

  Lemma Φ_reach_nonempty_sat X w k :
    length w = k →
    Φ_reach_nonempty X k (encode X w).
  Proof.
    intros <- B x δ ? ?.
    rewrite bool_decide_eq_true -reachable_from_spec -check_reachable_from_spec /=.
    setoid_rewrite reachable_from_spec.
    setoid_rewrite Φ_apply₁_spec. setoid_rewrite Φ_apply₂_spec.
    setoid_rewrite decode_encode.
    repeat apply ZifyClasses.or_morph.
    - rewrite slice_full_iff; try lia. done. admit.
    - by setoid_rewrite bool_decide_eq_true.
    - split.
      + intros [A [B' [φ [wr [? [Hr [? ?]]]]]]].
        exists A, B', φ, (length wr).
        rewrite bool_decide_eq_true. destruct wr as [|tk l].
        * rewrite /= slice_nil ?Nat.add_0_r; [lia|].
          rewrite app_nil_r in Hr.
          repeat split => //.
        * case_bool_decide => //. rewrite bool_decide_eq_true.
          have Hsub : sublist (slice w x δ ++ tk :: l) w by eapply reachable_sublist; eauto.
          apply sublist_slice in Hsub as [x' [? Hw']].
          rewrite app_length slice_length in Hw'; [lia|]. symmetry in Hw'.
          apply slice_app_inv_NoDup in Hw' as [Hwl Hwr] => //.
          2: { apply list_nonempty_length. rewrite slice_length; lia. }
          apply slice_eq_inv_NoDup in Hwl as [? _] => //.
          2: { apply list_nonempty_length. lia. } subst.
          rewrite slice_length in Hwr; first done.
          have Htmp : δ + length (tk :: l) - δ = length (tk :: l) by lia.
          rewrite Htmp in Hwr.
          symmetry in Hwr. rewrite slice_app Hwr.
          have HA : slice w (x + δ) (length (tk :: l)) ≠ [].
          { rewrite Hwr. naive_solver. }
          apply slice_nonempty_iff in HA.
          repeat split => //. admit. admit.
      + intros [A [B' [φ [δ' [? [? [Hr [Hd Hφ]]]]]]]].
        apply bool_decide_eq_true in Hr.
        exists A, B', φ, (slice w (x + δ) δ').
        rewrite slice_app_merge_2.
        repeat split => //.
        case_bool_decide; [by subst | by apply bool_decide_eq_true in Hd].
    - (* same as above *) admit.
  Admitted.

  Lemma apply_unary_nil (φ : unary_predicate Σ) :
    apply₁ φ [] = true.
  Proof. by destruct φ. Qed.

  Lemma apply_binary_nil_l (φ : binary_predicate Σ) w :
    apply₂ φ [] w = true.
  Proof. destruct φ; naive_solver. Qed.

  Lemma apply_binary_nil_r (φ : binary_predicate Σ) w :
    apply₂ φ w [] = true.
  Proof. destruct φ; naive_solver. Qed.

  Lemma Φ_reach_empty_sat k X w :
    length w = k →
    Φ_reach_empty X k (encode X w).
  Proof.
    intros <- B.
    rewrite bool_decide_eq_true -reachable_from_spec -check_reachable_from_spec /=.
    setoid_rewrite reachable_from_spec.
    setoid_rewrite bool_decide_eq_true.
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
    - (* same as above *) admit.
  Admitted.

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
      can_reach_from m B x δ = true → (* only this direction is needed *)
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
    setoid_rewrite Φ_apply₁_spec. setoid_rewrite Φ_apply₂_spec.
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
        rewrite app_nil_r. apply IHB; last naive_solver.
        eapply succ_left; eauto.
      * eapply reachable_from_left; eauto.
        2: eapply Φ_derive_spec; eauto; lia.
        rewrite slice_app_merge_2. apply IHδ => //; lia.
    - destruct Hr as [A [B' [φ [δ' [? [? [Hr [? ?]]]]]]]].
      case_bool_decide; subst; eapply reachable_from_right; eauto.
      * rewrite Nat.sub_0_r Nat.add_0_l in Hr. rewrite app_nil_l.
        apply IHB => //. eapply succ_right; eauto.
      * rewrite slice_merge_2. apply IHδ => //; lia.
      * eapply Φ_derive_spec; eauto; lia.
  Qed.

  Lemma Φ_reach_empty_spec S k m :
    Φ_derive k m →
    Φ_reach_nonempty S k m →
    Φ_reach_empty S k m →
    ∀ B,
      ε_can_reach_from m B = true → (* only this direction is needed *)
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
    flat_map (λ α, match α with
    | ε => [using_ε]
    | atom a => [using_atom a]
    | unary B φ => [using_unary B φ]
    | binary Bl Br φ => (λ δ', using_binary Bl Br φ δ') <$> (index_range δ ++ [δ])
    end) (clauses G A).

  Lemma elem_of_usable_clauses ψ A δ :
    ψ ∈ usable_clauses A δ ↔ match ψ with
    | using_ε => A ↦ ε ∈ G
    | using_atom a => A ↦ atom a ∈ G
    | using_unary B φ => A ↦ unary B φ ∈ G
    | using_binary Bl Br φ δ' => A ↦ binary Bl Br φ ∈ G ∧ δ' ≤ δ
    end.
  Admitted.

  Definition Φ_using_derive ψ x δ : formula :=
    match ψ with
    | using_ε => λ k m, δ = 0
    | using_atom a => λ k m, δ = 1 ∧ term m x = a
    | using_unary B φ => λ k m,
      if bool_decide (δ = 0) then G ⊨ B ⇒ []
      else Φ_apply₁ φ x δ k m ∧ can_derive m B x δ = true
    | using_binary Bl Br φ δ' => λ k m,
      (if bool_decide (δ' = 0) then G ⊨ Bl ⇒ [] else can_derive m Bl x δ' = true) ∧
      (if bool_decide (δ - δ' = 0) then G ⊨ Br ⇒ [] else can_derive m Br (x + δ') (δ - δ') = true) ∧
      Φ_apply₂ φ x δ' (x + δ') (δ - δ') k m
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
      + subst. rewrite slice_nil ?decode_length; [lia|].
        split.
        * intros [t [? [? ?]]]. exists t.
          rewrite witness_unary; eauto. repeat split => //. apply apply_unary_nil.
        * intros [t [? Ht]]. eapply witness_unary in Ht; eauto. naive_solver.
      + rewrite Φ_apply₁_spec.
        rewrite Φ_derive_spec; eauto; [|lia]. unfold derive.
        split.
        * intros [? [t [? [? ?]]]]. exists t.
          rewrite witness_unary; eauto. repeat split => //.
        * intros [t [? Ht]]. eapply witness_unary in Ht; eauto. naive_solver.
    - destruct Hψ as [Hψ ?]. unfold derive. rewrite Φ_apply₂_spec. repeat case_bool_decide.
      + have -> : δ = 0 by lia.
        have -> : slice (decode m k) x 0 = [] ++ [] by rewrite slice_nil ?decode_length; [lia|].
        have -> : δ' = 0 by lia. rewrite slice_nil ?decode_length; [lia|].
        split.
        * intros [[t1 [? [? ?]]] [[t2 [? [? ?]]] ?]]. exists t1, t2.
          rewrite witness_binary; eauto. repeat split => //.
        * intros [t1 [t2 [? [? [? Ht]]]]]. eapply witness_binary in Ht; eauto. naive_solver.
      + have -> : slice (decode m k) x δ = [] ++ slice (decode m k) x δ by rewrite app_nil_l.
        subst. rewrite Nat.add_0_r Nat.sub_0_r slice_nil ?decode_length; [lia|].
        rewrite Φ_derive_spec; eauto; [|lia]. unfold derive.
        split.
        * intros [[t1 [? [? ?]]] [[t2 [? [? ?]]] ?]]. exists t1, t2.
          rewrite witness_binary; eauto. repeat split => //.
        * intros [t1 [t2 [? [? [? Ht]]]]]. eapply witness_binary in Ht; eauto. naive_solver.
      + have -> : slice (decode m k) x δ = slice (decode m k) x δ ++ [] by rewrite app_nil_r.
        have -> : δ' = δ by lia. rewrite Nat.sub_diag slice_nil ?decode_length; [lia|].
        rewrite Φ_derive_spec; eauto; [|lia]. unfold derive.
        split.
        * intros [[t1 [? [? ?]]] [[t2 [? [? ?]]] ?]]. exists t1, t2.
          rewrite witness_binary; eauto. repeat split => //.
        * intros [t1 [t2 [? [? [? Ht]]]]]. eapply witness_binary in Ht; eauto. naive_solver.
      + have -> : slice (decode m k) x δ = slice (decode m k) x δ' ++ slice (decode m k) (x + δ') (δ - δ')
          by rewrite -slice_split.
        rewrite !Φ_derive_spec; eauto; [|lia..]. unfold derive.
        split.
        * intros [[t1 [? [? ?]]] [[t2 [? [? ?]]] ?]]. exists t1, t2.
          rewrite witness_binary; eauto. repeat split => //.
        * intros [t1 [t2 [? [? [? Ht]]]]]. eapply witness_binary in Ht; eauto. naive_solver.
  Qed.

  Definition Φ_multi_usable (A : N) (x δ : nat) : formula := λ k m,
    ∃ ψ1, ψ1 ∈ usable_clauses A δ ∧
      ∃ ψ2, ψ2 ∈ usable_clauses A δ ∧
        ψ1 ≠ ψ2 ∧ Φ_using_derive ψ1 x δ k m ∧ Φ_using_derive ψ2 x δ k m.

  Lemma wrap_with_id (P : Prop) :
    P ↔ id P.
  Proof. done. Qed.

  Ltac wrap H := apply ->wrap_with_id in H.

  Lemma app_length_le_l {A} (l1 l2 l : list A) :
    l1 ++ l2 = l →
    length l1 ≤ length l.
  Admitted.

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
      | [ H : _ ∧ _ |- _ ] => destruct H as [? ?]
      | [ H : ∃ _, _ |- _ ] => destruct H as [? ?]
      end.
      all: simpl in *; try congruence.
      all: repeat match goal with
      | [ H : ?t ▷ ?A ={?G}=> ?w |- ∃ t, t ▷ ?A ={?G}=> ?w ∧ _ ] =>
        exists t; split; [by apply H|]; clear H
      end => //.
      admit. admit.
    - (* <- *)
      intros [t1 [[? [? Ht1]] [t2 [[? [? Ht2]] ?]]]].
      destruct t1; destruct t2.
      all: simpl in *; try done; try congruence.
      all: inversion Ht1; subst; clear Ht1.
      all: inversion Ht2; subst; clear Ht2.
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
        intros Heq. inversion Heq; subst; clear Heq.
        have Hw : word t1_1 ++ word t1_2 = word t2_1 ++ word t2_2 by congruence.
        apply app_inj_1 in Hw => //. naive_solver.
      }
      all: try (split; eapply Φ_using_derive_witness; simpl; eauto).
      all: repeat match goal with
      | [ |- _ ▷ _ ={ _ }=> _ ] =>
        repeat split; simpl; try done; try congruence; econstructor; eauto
      | [ H : [] = slice (decode _ _) _ ?δ |- ?δ = 0 ∧ _ ] =>
        rewrite -H; symmetry in H; apply slice_nil_iff in H; [|by rewrite decode_length]; split; first done
      | [ H : [_] = slice (decode _ _) _ ?δ |- ?δ = 1 ∧ _ = term _ _ ∧ _ ] =>
        rewrite -H; symmetry in H; apply slice_singleton_iff in H;
        let H' := fresh in destruct H as [-> H']; rewrite decode_lookup in H'; [lia|];
        inversion H'; subst; clear H'; do 2 (split; first done)
      | [ |- ∃ t, root t = root ?t' ∧ _ ] =>
        exists t'; split; first done
      | [ |- ∃ t1 t2, root t1 = root ?t1' ∧ root t2 = root ?t2' ∧ _ ] =>
        exists t1', t2'; do 2 (split; first done)
      | [ |- word ?t = slice (decode _ _) _ _ ∧ _ ] =>
        split; first by eapply slice_app_inv_NoDup_l; eauto
      end.
  Admitted.

  (* Main theorems *)

  Definition Φ_amb A : formula := λ k m,
    Φ_derive k m ∧ Φ_reach A k m ∧ ∃ H,
     (ε_can_reach_from m H = true ∧ Φ_multi_usable H 0 0 k m) ∨
     (∃ x δ, 0 < δ ∧ x + δ ≤ k ∧ can_reach_from m H x δ = true ∧ Φ_multi_usable H x δ k m).

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
    - left. rewrite bool_decide_eq_true. split; first done.
      eapply Φ_multi_usable_spec; eauto; lia.
    - right.
      have Hsub : sublist (tk :: h) w by eapply reachable_sublist; eauto.
      apply sublist_slice in Hsub as [x [? Hh]].
      exists x, (length (tk :: h)).
      rewrite bool_decide_eq_true -Hh. repeat split => //.
      1: rewrite cons_length; lia.
      eapply Φ_multi_usable_spec; eauto; try congruence.
      rewrite decode_encode -Hh; eauto.
  Qed.

End encoding.