From stdpp Require Import relations.
From Coq Require Import ssreflect.
From ambig Require Import grammar decidability util ambiguity acyclic sub_derive.

Section encoding.

  Variable Σ N : Type.
  Context `{!EqDecision Σ}.
  Context `{!EqDecision N}.

  Variable G : grammar Σ N.
  Context `{!acyclic G}.

  (* sat model *)

  Record model := {
    term : nat → Σ;
    line : nat → nat;
    col : nat → nat;
    line_col i := (line i, col i);
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

  (* TODO: since the encoding has a similar shape to the proof rules for G ⊨ A ⇒ w, 
     we can define those proof rules first using `Inductive`, and then a first-order logic
     proposition using disjunction, and show they are equiv to the original definition.

     In this way, it suffices to show two propositions both using disjunction, but one is using
     `can_derive` and the other `_ ⊨ _ ⇒ _`, are equiv.

     This approach will also simplifies the proof for `Φ_derive k (decode _ w)`, given that
     all `can_derive` is defined as `bool_decide (_ ⊨ _ ⇒ _)`.
  *)
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

  (* encoding reachable from (S, [0..k]) *)
  Definition Φ_reach k S : formula := λ m,
    ∀ B x δ, (* δ can be zero *) x + δ ≤ k →
      can_reach_from m B x δ = true ↔ (
        (B = S ∧ x = 0 ∧ δ = k) ∨
        (∃ A φ, A ↦ unary B φ ∈ G ∧ can_reach_from m A x δ = true ∧ apply₁ φ (decode m x δ) = true) ∨
        (∃ A B' φ δ', x + δ + δ' ≤ k ∧ A ↦ binary B B' φ ∈ G ∧ can_reach_from m A x (δ + δ') = true ∧
          (if bool_decide (δ' = 0) then G ⊨ B' ⇒ [] else can_derive m B' (x + δ) δ' = true) ∧
          apply₂ φ (decode m x δ) (decode m (x + δ) δ') = true) ∨
        (∃ A B' φ δ', δ' ≤ x (* TODO *) ∧ A ↦ binary B' B φ ∈ G ∧ can_reach_from m A (x - δ') (δ' + δ) = true ∧
          (if bool_decide (δ' = 0) then G ⊨ B' ⇒ [] else can_derive m B' (x - δ') δ' = true) ∧
          apply₂ φ (decode m (x - δ') δ') (decode m x δ) = true)
      ).

  Lemma Φ_reach_spec k S m :
    Φ_derive k m →
    Φ_reach k S m →
    ∀ B x δ, x + δ ≤ k →
      can_reach_from m B x δ = true ↔ reachable G (S, decode m 0 k) (B, decode m x δ).
  Proof.
    intros HΦ' HΦ B x δ ?. rewrite -reachable_from_spec.
    (* induction on range length *)
    generalize dependent B.
    generalize dependent x.
    induction δ as [δ IHδ] using (induction_ltof1 _ (λ δ, k - δ)) => x Hk B.
    unfold ltof in IHδ.
    (* induction on nonterminal *)
    have Hwf : wf (succ G) by apply acyclic_succ_wf.
    induction B as [B IHB] using (well_founded_induction Hwf).
    rewrite HΦ; last done.
    split.
    - (* -> *) 
      intros [Hr|[Hr|[Hr|Hr]]].
      + destruct Hr as [-> [-> ->]]. apply reachable_from_refl.
      + destruct Hr as [A [φ [? [? ?]]]].
        eapply reachable_from_unary; eauto.
        apply IHB => //. eapply succ_unary; eauto.
      + destruct Hr as [A [B' [φ [δ' [? [? [? [? ?]]]]]]]].
        case_bool_decide; subst.
        * eapply reachable_from_left; eauto.
          rewrite app_nil_r. apply IHB; last naive_solver.
          eapply succ_left; eauto.
        * eapply reachable_from_left; eauto.
          2: eapply Φ_derive_spec; eauto; lia.
          rewrite decode_merge. apply IHδ => //; lia.
      + destruct Hr as [A [B' [φ [δ' [? [? [Hr [? ?]]]]]]]].
        case_bool_decide; subst; eapply reachable_from_right; eauto.
        * rewrite Nat.sub_0_r Nat.add_0_l in Hr. rewrite app_nil_l.
          apply IHB => //. eapply succ_right; eauto.
        * have Hx : x = x - δ' + δ' by lia.
          rewrite {2}Hx decode_merge. apply IHδ => //; lia.
        * eapply Φ_derive_spec; eauto; lia.
    - (* <- *)
      inversion 1; subst.
      + left.
        have Hl : length (decode m 0 k) = length (decode m x δ) by congruence.
        rewrite !decode_length in Hl.
        split => //. lia.
      + right; left.
        exists A, φ. repeat split => //.
        apply IHB => //. eapply succ_unary; eauto.
      + right; right; left.
        have H3' := H3.
        apply reachable_from_spec, reachable_sublist in H3 => //.
        have Hw2 : w2 = decode m (x + δ) (length w2). admit.
        have Hw2l : x + δ + length w2 ≤ k. admit.
        exists A, Br, φ, (length w2). repeat split => //.
        * destruct w2 => /=.
          rewrite app_nil_r in H3'. rewrite Nat.add_0_r. apply IHB => //.
          eapply succ_left; eauto.
          rewrite cons_length in Hw2. rewrite cons_length in Hw2l.
          apply IHδ; [lia.. | by rewrite -decode_merge -Hw2].
        * destruct w2 => //=.
          eapply Φ_derive_spec; eauto. lia.
          rewrite cons_length in Hw2. by rewrite -Hw2.
        * by rewrite -Hw2.
      + right; right; right.
        have H3' := H3.
        apply reachable_from_spec, reachable_sublist in H3 => //.
        have Hw1 : w1 = decode m (x - length w1) (length w1). admit.
        have Hw1l : length w1 ≤ x. admit.
        exists A, Bl, φ, (length w1). repeat split => //.
        * destruct w1 => /=.
          rewrite app_nil_l in H3'. rewrite Nat.sub_0_r. apply IHB => //.
          eapply succ_right; eauto.
          rewrite cons_length in Hw1. rewrite cons_length in Hw1l.
          apply IHδ; [lia.. | ].
          have -> : Datatypes.S (length w1 + δ) = (Datatypes.S (length w1)) + δ by lia.
          rewrite -decode_merge Nat.sub_add //.
          by rewrite Hw1 in H3'.
        * destruct w1 => //=.
          eapply Φ_derive_spec; eauto. lia.
          rewrite Nat.sub_add //. lia.
          rewrite cons_length in Hw1. by rewrite -Hw1.
        * by rewrite -Hw1.
    Admitted.

  (* decode properties *)

  Lemma decode_empty m x δ :
    decode m x δ = [] ↔ δ = 0.
  Proof.
    (* intros H. *)
    (* have : length (decode m x δ) = length [] by rewrite H. *)
    (* rewrite decode_length. naive_solver. *)
  Admitted.

  Lemma decode_singleton m x δ a p :
    decode m x δ = [a @ p] →
    δ = 1 ∧ a = term m x ∧ p = (line m x, col m x).
  Proof.
    intros H.
  Admitted.

  Lemma decode_app_l m x δ w1 w2 :
    decode m x δ = w1 ++ w2 →
    decode m x (length w1) = w1.
  Admitted.

  (* encoding derivations of different prologue *)

  Inductive prologue : Type :=
  | pro_ε
  | pro_atom (a : Σ)
  | pro_unary (A : N)
  | pro_binary (A B : N) (δ : nat) (* length of first part *)
  .

  Local Instance prologue_elem_of_nonterm : ElemOf prologue N := λ ψ A,
    match ψ with
    | pro_ε => A ↦ ε ∈ G
    | pro_atom a => A ↦ atom a ∈ G
    | pro_unary B => ∃ φ, A ↦ unary B φ ∈ G
    | pro_binary Bl Br _ => ∃ φ, A ↦ binary Bl Br φ ∈ G
    end.

  Definition Φ_pro ψ A x δ : formula := λ m,
    match ψ with
    | pro_ε => δ = 0
    | pro_atom a => δ = 1 ∧ a = term m x
    | pro_unary B =>
      match δ with
      | 0 => G ⊨ B ⇒ []
      | _ => can_derive m B x δ = true ∧
        apply₁ (unary_clause_predicate _ _ G A B) (decode m x δ) = true
      end
    | pro_binary Bl Br δ' =>
      match δ', δ - δ' with
      | 0, _ => G ⊨ Bl ⇒ [] ∧ can_derive m Br x δ = true
      | _, 0 => can_derive m Bl x δ' = true ∧ G ⊨ Br ⇒ []
      | _, _ => can_derive m Bl x δ' = true ∧ 
        can_derive m Br (x + δ') (δ - δ') = true ∧
        apply₂ (binary_clause_predicate _ _ G A Bl Br) (decode m x δ') (decode m (x + δ') (δ - δ')) = true
      end
    end.

  (* Definition Φ_binary_derive Bl Br φ x δl δr : formula := λ m,
    match δl, δr with
    | 0, _ => G ⊨ Bl ⇒ [] ∧ can_derive m Br x δr = true
    | _, 0 => can_derive m Bl x δl = true ∧ G ⊨ Br ⇒ []
    | _, _ => can_derive m Bl x δl = true ∧ can_derive m Br (x + δl) δr = true ∧
      apply₂ φ (decode m x δl) (decode m (x + δl) δr) = true
    end.

  Lemma Φ_binary_derive_witness k m x δl δr A Bl Br φ :
    Φ_derive k m →
    x + δl + δr ≤ k →
    A ↦ binary Bl Br φ ∈ G →
    Φ_binary_derive Bl Br φ x δl δr m ↔
      ∃ t1 t2, root t1 = Bl ∧ root t2 = Br ∧ word t1 = decode m x δl ∧
        (binary_tree A t1 t2) ▷ A ={G}=> decode m x (δl + δr). *)
  (* Proof.
    intros ? ? ? ? ? [Hdl [Hdr ?]].
    eapply Φ_derive_spec in Hdl as [t1 [? [? ?]]]; eauto; try lia.
    eapply Φ_derive_spec in Hdr as [t2 [? [? ?]]]; eauto; try lia.
    exists t1, t2. repeat split => //.
    have ? : decode m x δ' ++ decode m (x + δ') (δ - δ') = decode m x δ.
    { rewrite decode_merge. by have -> : δ' + (δ - δ') = δ by lia. }
    repeat split. simpl in *. congruence.
    econstructor => //. naive_solver. by rewrite H9 H6.
  Qed. *)
(* 
  Definition Φ_clause_derive (α : clause Σ N) (x δ : nat) : formula := λ m,
    match α with
    | ε => δ = 0
    | atom a => δ = 1 ∧ term m x = a
    | unary A φ =>
      match δ with
      | 0 => G ⊨ A ⇒ []
      | _ => can_derive m A x δ = true ∧ apply₁ φ (decode m x δ) = true
      end
    | binary Bl Br φ => ∃ δl δr,
      δl + δr = δ ∧ Φ_binary_derive Bl Br φ x δl δr m
    end. *)

  Ltac solve_witness :=
    repeat split; simpl; try done; try congruence;
    econstructor; eauto.

  Lemma Φ_pro_witness k m x δ A ψ :
    Φ_derive k m →
    x + δ ≤ k →
    ψ ∈ A →
    Φ_pro ψ A x δ m ↔ match ψ with
      | pro_ε => δ = 0 ∧ ε_tree A ▷ A ={G}=> decode m x δ
      | pro_atom a => δ = 1 ∧ a = term m x ∧ let p := (line m x, col m x) in
        (token_tree A (a @ p)) ▷ A ={G}=> decode m x δ
      | pro_unary B => ∃ t, root t = B ∧ (unary_tree A t) ▷ A ={G}=> decode m x δ
      | pro_binary Bl Br δ' => ∃ t1 t2, root t1 = Bl ∧ root t2 = Br ∧
        word t1 = decode m x δ' ∧ (binary_tree A t1 t2) ▷ A ={G}=> decode m x δ
      end.
  Proof.
    intros ? ? Hψ. case_match => /=; split.
    all: simpl in Hψ.
    - intros ->. solve_witness.
    - naive_solver.
    - intros [-> ->]. solve_witness.
    - naive_solver.
    - destruct Hψ as [φ ?].
      case_match.
      * intros [t [? [? ?]]]. subst. exists t. solve_witness.
        destruct φ as [φ ?]. simpl. congruence.
      * intros [? ?].
        eapply Φ_derive_spec in H2 as [t [? [? ?]]]; eauto; try lia.
        subst. exists t. solve_witness.
        have ? : unary_clause_predicate Σ N G A (root t) = φ. admit.
        congruence.
    - destruct Hψ as [φ ?].
      intros [t [? [? [? Ht]]]]. inversion Ht; subst; clear Ht.
      case_match. 2: split.
      * exists t. solve_witness.
      * eapply Φ_derive_spec; eauto; try lia. exists t. solve_witness.
      * have ? : word (unary_tree A t) = word t by done.
        have ? : unary_clause_predicate Σ N G A (root t) = φ0. admit.
        congruence.
    - destruct Hψ as [φ ?]. repeat case_match.
  Admitted.

  Definition Φ_multi (A : N) (x δ : nat) : formula := λ m,
    ∃ ψ1, ψ1 ∈ A ∧
     ∃ ψ2, ψ2 ∈ A ∧ ψ1 ≠ ψ2 ∧ Φ_pro ψ1 A x δ m ∧ Φ_pro ψ2 A x δ m.

  Lemma wrap_with_id (P : Prop) :
    P ↔ id P.
  Proof. done. Qed.

  Ltac wrap H := apply ->wrap_with_id in H.

  Lemma Φ_multi_spec k m x δ A :
    Φ_derive k m →
    x + δ ≤ k →
    Φ_multi A x δ m ↔ ∃ t1, t1 ▷ A ={G}=> decode m x δ ∧
      ∃ t2, t2 ▷ A ={G}=> decode m x δ ∧ ¬ similar t1 t2.
  Proof.
    intros ? ?. split.
    - (* -> *)
      intros [ψ1 [ψ2 [? [? [? [Hψ1 Hψ2]]]]]].
      eapply Φ_pro_witness in Hψ1; eauto.
      eapply Φ_pro_witness in Hψ2; eauto.
      repeat case_match.
      all: repeat match goal with
      | [ H : _ ∧ _ |- _ ] => destruct H as [? ?]
      | [ H : ∃ _, _ |- _ ] => destruct H as [? ?]
      end.
      all: simpl in *; try congruence.
      all: repeat match goal with
      | [ H : ?t ▷ ?A ={?G}=> ?w |- ∃ t, t ▷ ?A ={?G}=> ?w ∧ _ ] =>
        exists t; split; [by apply H|]; clear H
      end => //.
      + congruence. 
      + simpl. intros [? [? ?]]; subst.
        have Hl : length (decode m x δ1) = length (decode m x δ0)
          by f_equal; congruence.
        rewrite !decode_length in Hl. congruence.
    - (* <- *)
      intros [t1 [[? [? Ht1]] [t2 [[? [? Ht2]] ?]]]].
      destruct t1; destruct t2.
      all: simpl in *; try done; try congruence.
      all: inversion Ht1; subst; clear Ht1.
      all: inversion Ht2; subst; clear Ht2.
      all: unfold Φ_multi.
      all: repeat match goal with
      | [ H : ?A ↦ ε ∈ _ |- ∃ ψ, ψ ∈ ?A ∧ _ ] =>
        assert (pro_ε ∈ A) by (apply H);
        exists pro_ε; split; [done|]; wrap H
      | [ H : ?A ↦ atom ?a ∈ _ |- ∃ ψ, ψ ∈ ?A ∧ _ ] =>
        assert (pro_atom a ∈ A) by (apply H);
        exists (pro_atom a); split; [done|]; wrap H
      | [ H : ?A ↦ unary ?B ?φ ∈ _ |- ∃ ψ, ψ ∈ ?A ∧ _ ] =>
        assert (pro_unary B ∈ A) by (by exists φ);
        exists (pro_unary B); split; [done|]; wrap H
      | [ H : ?A ↦ binary (root ?t1) (root ?t2) ?φ ∈ _ |- ∃ ψ, ψ ∈ ?A ∧ _ ] =>
        assert (pro_binary (root t1) (root t2) (length (word t1)) ∈ A) by (by exists φ);
        exists (pro_binary (root t1) (root t2) (length (word t1)));
        split; [done|]; wrap H
      end.
      all: split; first try congruence.
      12: {
        intros Heq. inversion Heq; subst; clear Heq.
        have Hw : word t1_1 ++ word t1_2 = word t2_1 ++ word t2_2 by congruence.
        apply app_inj_1 in Hw => //. naive_solver.
      }
      all: try (split; eapply Φ_pro_witness; simpl; eauto).
      all: repeat match goal with
      | [ |- _ ▷ _ ={ _ }=> _ ] =>
        repeat split; simpl; try done; try congruence; econstructor; eauto
      | [ H : [] = decode _ _ ?δ |- ?δ = 0 ∧ _ ] =>
        symmetry in H; rewrite H; apply decode_empty in H;
        split; first done
      | [ H : [_] = decode _ _ ?δ |- ?δ = 1 ∧ _ = term _ _ ∧ _ ] =>
        symmetry in H; rewrite H; apply decode_singleton in H as [? [? ?]];
        do 2 (split; first done)
      | [ |- word ?t = decode _ _ _ ∧ _ ] =>
        split; first by erewrite decode_app_l; eauto
      | [ |- ∃ t, root t = root ?t' ∧ _ ] =>
        exists t'; split; first done
      | [ |- ∃ t1 t2, root t1 = root ?t1' ∧ root t2 = root ?t2' ∧ _ ] =>
        exists t1', t2'; do 2 (split; first done)
      end.
  Qed.

  (* Main theorems *)

  Definition Φ_amb A k : formula := λ m,
    Φ_derive k m ∧ Φ_reach k A m ∧ ∃ H x δ, x + δ ≤ k ∧
      can_reach_from m H x δ = true ∧ Φ_multi H x δ m.

  Theorem Φ_amb_sound A k m :
    Φ_amb A k m → derive_amb G A (decode m 0 k).
  Admitted.

  Variable error_letter : Σ.
  Implicit Type w : sentence Σ.

  Fixpoint slice w x δ : sentence Σ :=
    match δ with
    | 0 => []
    | S n =>
      match w !! x with
      | Some tk => tk :: slice w (x + 1) n
      | None => []
      end
    end.

  (* TODO: why this instance cannot be found? *)
  (* Check acyclic_derive_dec. *)
  (* Check acyclic_reachable_dec. *)

  Global Instance acyclic_derive_dec A w :
    Decision (G ⊨ A ⇒ w).
  Admitted.

  Global Instance acyclic_reachable_dec A w H h :
    Decision (reachable G (A, w) (H, h)).
  Admitted.

  Definition encode (w : sentence Σ) S : model := {|
    term i :=
      match w !! i with
      | Some (a @ _) => a
      | None => error_letter
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
    can_derive A x δ := bool_decide (G ⊨ A ⇒ (slice w x δ));
    can_reach_from A x δ := bool_decide (reachable G (S, w) (A, slice w x δ));
  |}.

  Lemma reachable_sub_word A w H h :
    reachable G (A, w) (H, h) →
    ∃ w1 w2, w = w1 ++ h ++ w2.
  Admitted.

  Theorem Φ_amb_complete A k w :
    length w = k →
    derive_amb G A w →
    ∃ m, Φ_amb A k m (* ∧ decode m 0 k = w *).
  Proof.
    intros Hk Hamb.
    apply derive_amb_iff_local_amb in Hamb; eauto.
    destruct Hamb as [H [h [Hr [t1 [t2 [Ht1 [Ht2 Hne]]]]]]].
    exists (encode w A).
    have HΦ : Φ_derive k (encode w A).
    { intros ?????. simpl. rewrite !bool_decide_eq_true. admit. }
    have HΦ' : Φ_reach k A (encode w A).
    { intros ????. simpl. rewrite !bool_decide_eq_true. admit. }
    split => //. split => //.
    have Hr' := Hr.
    apply reachable_sub_word in Hr' as [w1 [w2 Hw]].
    exists H, (length w1), (length h).
    have ? : length w1 + length h ≤ k by admit.
    split => //.
    split. rewrite bool_decide_eq_true. admit. (* slice lemma *)
    admit. (* multi_derive_encoding complete *)
  Admitted.

End encoding.