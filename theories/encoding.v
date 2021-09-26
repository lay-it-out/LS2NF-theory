From stdpp Require Import relations.
From Coq Require Import ssreflect.
From ambig Require Import grammar acyclic reachable ambiguity.

(* sat model *)

Record model (Σ N : Type) := {
  tok : nat → Σ;
  line : nat → nat;
  col : nat → nat;
  can_derive : N → nat (* start (inclusive) *) → nat (* length *) → bool;
  can_reach : N → nat (* start (inclusive) *) → nat (* length *) → N → nat → nat → bool;
}.

Arguments tok {_} {_}.
Arguments line {_} {_}.
Arguments col {_} {_}.
Arguments can_derive {_} {_}.
Arguments can_reach {_} {_}.

Fixpoint decode {Σ N : Type} (m : model Σ N) (x δ : nat) : sentence Σ :=
  match δ with
  | 0 => []
  | S n => tok m x @ (line m x, col m x) :: decode m (S x) n
  end.

Lemma decode_merge {Σ N : Type} (m : model Σ N) x δ δ' :
  decode m x δ ++ decode m (x + δ) δ' = decode m x (δ + δ').
Proof.
  generalize dependent x.
  induction δ as [|n IHn] => x /=.
  - by rewrite -plus_n_O.
  - rewrite <- IHn.
    have -> : x + S n = S x + n by lia.
    done.
Qed.

(* encoding derivation *)

Definition derive_encoding {Σ N : Type} (G : grammar Σ N) (m : model Σ N) (k : nat) : Prop :=
  ∀ x δ A, x + δ ≤ k →
    can_derive m A x δ →
    (δ = 1 ∧ ∃ a, A ↦ atom a ∈ G ∧ tok m x = a) ∨
    (∃ B φ, A ↦ unary B φ ∈ G ∧ can_derive m B x δ ∧ φ (decode m x δ)) ∨
    (∃ B E φ, A ↦ binary B E φ ∈ G ∧ nullable G E ∧ can_derive m B x δ) ∨
    (∃ E B φ, A ↦ binary E B φ ∈ G ∧ nullable G E ∧ can_derive m B x δ) ∨
    (δ > 1 ∧ ∃ δ' B1 B2 φ, 0 < δ' < δ ∧ A ↦ binary B1 B2 φ ∈ G ∧
      can_derive m B1 x δ' ∧ can_derive m B2 (x + δ') (δ - δ') ∧
      φ (decode m x δ') (decode m (x + δ') (δ - δ'))).

Lemma derive_encoding_sound {Σ N} (G : grammar Σ N) m k :
  acyclic G →
  derive_encoding G m k →
  ∀ x δ A, x + δ ≤ k →
    can_derive m A x δ → G ⊨ A ⇒ decode m x δ.
Proof.
  intros HG Hf x δ A Hk.
  (* induction on range length *)
  generalize dependent A.
  generalize dependent x.
  induction δ as [δ IHδ] using lt_wf_ind.
  intros x Hk A.
  (* induction on nonterminal *)
  apply acyclic_succ_flip_wf in HG.
  induction A as [A IHA] using (well_founded_induction HG).
  (* specialize should after induction, otherwise the inductive hypothesis will mention these conditions *)
  intros HA. specialize (Hf _ _ _ Hk HA).
  repeat destruct Hf as [Hf | Hf].
  - destruct Hf as [-> [a [? ?]]].
    apply derive_atom. naive_solver.
  - destruct Hf as [B [φ [? [? ?]]]].
    eapply derive_unary; eauto.
    clear IHδ. eapply IHA; eauto. eapply succ_unary; eauto.
  - destruct Hf as [B [E [φ [? [? ?]]]]].
    rewrite <- app_nil_r.
    eapply derive_binary; eauto.
    * apply (binary_predicate_axiom G). naive_solver.
    * clear IHδ. eapply IHA; eauto. eapply succ_left; eauto.
    * by apply nullable_spec.
  - destruct Hf as [E [B [φ [? [? ?]]]]].
    rewrite <- app_nil_l.
    eapply derive_binary; eauto.
    * apply (binary_predicate_axiom G). naive_solver.
    * by apply nullable_spec.
    * clear IHδ. eapply IHA; eauto. eapply succ_right; eauto.
  - destruct Hf as [? [δ' [B1 [B2 [φ [? [? [? [? ?]]]]]]]]].
    have -> : δ = δ' + (δ - δ') by lia.
    rewrite -decode_merge.
    eapply derive_binary; eauto. clear IHA.
    all: apply IHδ; auto; lia.
Qed.

(* encoding reachability *)

Definition reachable_encoding {Σ N : Type} (G : grammar Σ N) (m : model Σ N) (k : nat) : Prop :=
  ∀ A x δ H xH δH, x + δ ≤ k → xH + δH ≤ k →
    can_reach m A x δ H xH δH →
    (A = H ∧ xH = x ∧ δH = δ) ∨
    (∃ B φ, A ↦ unary B φ ∈ G ∧ can_reach m B x δ H xH δH = true ∧ φ (decode m x δ)) ∨
    (∃ Bl Br φ δ', 0 < δ' < δ ∧ A ↦ binary Bl Br φ ∈ G ∧ can_reach m Bl x δ' H xH δH ∧
      can_derive m Br (x + δ') (δ - δ') ∧ φ (decode m x δ') (decode m (x + δ') (δ - δ'))) ∨
    (∃ Bl Br φ δ', 0 < δ' < δ ∧ A ↦ binary Bl Br φ ∈ G ∧ can_reach m Br (x + δ') (δ - δ') H xH δH ∧
      can_derive m Bl x δ' ∧ φ (decode m x δ') (decode m (x + δ') (δ - δ'))).

Lemma reachable_encoding_sound {Σ N : Type} G (m : model Σ N) k :
  acyclic G →
  derive_encoding G m k ∧ reachable_encoding G m k →
  ∀ A x δ H xH δH, x + δ ≤ k → xH + δH ≤ k →
    can_reach m A x δ H xH δH → reachable G A (decode m x δ) H (decode m xH δH).
Proof.
  intros HG [Hm Hr] A x δ H xH δH.
  (* induction on range length *)
  generalize dependent A.
  generalize dependent x.
  induction δ as [δ IHδ] using lt_wf_ind.
  intros x A Hk1 Hk2.
  (* induction on nonterminal *)
  induction A as [A IHA] using (well_founded_induction (acyclic_succ_flip_wf _ HG)).
  (* specialize should after induction, otherwise the inductive hypothesis will mention these conditions *)
  intros HA. specialize (Hr _ _ _ _ _ _ Hk1 Hk2 HA).
  repeat destruct Hr as [Hr | Hr].
  - destruct Hr as [-> [-> ->]].
    by constructor.
  - destruct Hr as [B [φ [? [? ?]]]].
    eapply reachable_unary; eauto.
    clear IHδ. eapply IHA; eauto. eapply succ_unary; eauto.
  - destruct Hr as [Bl [Br [φ [δ' [? [? [? [? ?]]]]]]]].
    have -> : δ = δ' + (δ - δ') by lia.
    rewrite -decode_merge.
    eapply reachable_left; eauto.
    * clear IHA. apply IHδ; [lia.. | done].
    * eapply derive_encoding_sound; eauto. lia.
  - destruct Hr as [Bl [Br [φ [δ' [? [? [? [? ?]]]]]]]].
    have -> : δ = δ' + (δ - δ') by lia.
    rewrite -decode_merge.
    eapply reachable_right; eauto.
    * clear IHA. apply IHδ; [lia.. | done].
    * eapply derive_encoding_sound; eauto. lia.
Qed.

(* encoding ambiguous derivation *)

(*
Inductive ψ_formula (Σ N : Type) : Type :=
  | ψ_atom : Σ → ψ_formula Σ N
  | ψ_unary : N → unary_predicate Σ → ψ_formula Σ N
  | ψ_binary_null_l : N → N → binary_predicate Σ → ψ_formula Σ N
  | ψ_binary_null_r : N → N → binary_predicate Σ → ψ_formula Σ N
  | ψ_binary : N → N → binary_predicate Σ → ψ_formula Σ N
  .

Arguments ψ_atom {_} {_}.
Arguments ψ_unary {_} {_}.
Arguments ψ_binary_null_l {_} {_}.
Arguments ψ_binary_null_r {_} {_}.
Arguments ψ_binary {_} {_}.

Definition ψ_sat {Σ N : Type} (ψ : ψ_formula Σ N) (m : model Σ N) (δ : nat) : Prop :=
  match ψ with
  | ψ_atom a => δ = 0 ∧ tok m 0 = a
  | ψ_unary A φ => can_derive m A 0 δ = true ∧ φ (decode m 0 δ)
  | ψ_binary_null_l _ A _ => can_derive m A 0 δ = true
  | ψ_binary_null_r A _ _ => can_derive m A 0 δ = true
  | ψ_binary B1 B2 φ => ∃ δ', δ' < δ ∧
    can_derive m B1 0 δ' = true ∧
    can_derive m B2 (δ' + 1) (δ - δ' - 1) = true ∧
    φ (decode m 0 δ') (decode m (δ' + 1) (δ - δ' - 1))
  end.

Definition ψ_intro {Σ N : Type} (G : grammar Σ N) (A : N) : list (ψ_formula Σ N) :=
  flat_map (λ α,
    match α with
    | ε => []
    | atom a => [ψ_atom a]
    | unary A φ => [ψ_unary A φ]
    | binary A B φ =>
      (if nullable G A then [ψ_binary_null_l A B φ] else []) ++
      (if nullable G B then [ψ_binary_null_r A B φ] else []) ++
      [ψ_binary A B φ]
    end) (P G A).

Lemma elem_of_ψ_intro {Σ N : Type} (ψ : ψ_formula Σ N) G A :
  ψ ∈ ψ_intro G A →
  match ψ with
  | ψ_atom a => G ⊢ A ↦ atom a
  | ψ_unary B φ => G ⊢ A ↦ unary B φ
  | ψ_binary_null_l B C φ => nullable G B = true ∧ G ⊢ A ↦ binary B C φ
  | ψ_binary_null_r B C φ => nullable G C = true ∧ G ⊢ A ↦ binary B C φ
  | ψ_binary B C φ => G ⊢ A ↦ binary B C φ
  end.
Admitted.

Definition amb_encoding {Σ N : Type} (G : grammar Σ N) (m : model Σ N) (k : nat) : Prop :=
  membership_formula G m k ∧ ∃ δ A, δ < k ∧ can_derive m A 0 δ = true ∧
    let Ψ := ψ_intro G A in ∃ ψ_1 ψ_2, ψ_1 ≠ ψ_2 ∧
      ψ_1 ∈ Ψ ∧ ψ_2 ∈ Ψ ∧ ψ_sat ψ_1 m δ ∧ ψ_sat ψ_2 m δ.

Lemma ψ_witness {Σ N : Type} (G : grammar Σ N) `{!Acyclic G} (m : model Σ N) k δ A ψ :
  membership_formula G m k →
  0 < k →
  δ < k →
  can_derive m A 0 δ = true →
  ψ ∈ ψ_intro G A →
  ψ_sat ψ m δ →
  let w := decode m 0 δ in
  match ψ with
  | ψ_atom a => ∃ tk, w = [tk] ∧ (tok_tree A tk) ▷ A ={G}=> w
  | ψ_unary B φ => ∃ t, (unary_tree A t) ▷ A ={G}=> w
  | ψ_binary_null_l B C φ => ∃ tε t, (binary_tree A tε t) ▷ A ={G}=> w
  | ψ_binary_null_r B C φ => ∃ t tε, (binary_tree A t tε) ▷ A ={G}=> w
  | ψ_binary B C φ => ∃ t1 t2, (binary_tree A t1 t2) ▷ A ={G}=> w
  end.
Proof.
  intros H ? ? HA Hin Hsat.
  apply elem_of_ψ_intro in Hin.
  assert (He : ∀ x δ, x + δ < k → ∀ A, can_derive m A x δ = true → G ⊨ A ⇒ decode m x δ).
  { intros ? ?. eapply encode_sound; eauto. }
  destruct ψ as [b | B φ | B C φ | B C φ | B C φ]; simpl in Hsat.
  - destruct Hsat as [-> ?].
    exists (tok m 0 @ (line m 0, col m 0)).
    split; first done.
    apply tok_tree_witness. congruence.
  - destruct Hsat as [HB Hφ].
    destruct (He 0 δ ltac:(lia) _ HB) as [t Ht].
    exists t.
    eapply unary_tree_witness; eauto.
  - destruct Hin as [HB ?].
    destruct (nullable_spec _ _ HB) as [tε Htε].
    rename Hsat into HC.
    destruct (He 0 δ ltac:(lia) _ HC) as [t Ht].
    exists tε, t. rewrite <- app_nil_l.
    by eapply binary_tree_witness; eauto.
  - rename Hsat into HB.
    destruct (He 0 δ ltac:(lia) _ HB) as [t Ht].
    destruct Hin as [HC ?].
    destruct (nullable_spec _ _ HC) as [tε Htε].
    exists t, tε. rewrite <- app_nil_r.
    by eapply binary_tree_witness; eauto.
  - destruct Hsat as [δ' [? [HB [HC ?]]]].
    destruct (He 0 δ' ltac:(lia) _ HB) as [t1 Ht1].
    destruct (He (δ' + 1) (δ - δ' - 1) ltac:(lia) _ HC) as [t2 Ht2].
    exists t1, t2.
    erewrite <- decode_merge.
    + eapply binary_tree_witness; eauto.
    + done.
Qed.

Ltac split_exist_and :=
  repeat match goal with
  | [ H : ∃ _, _ ∧ _ ∧ _ |- _ ] => destruct H as [? [? [? ?]]]
  | [ H : ∃ _, _ ∧ _ |- _ ] => destruct H as [? [? ?]]
  | [ H : ∃ _, _ |- _ ] => destruct H as [? ?]
  | [ H : ∃ _ _, _ ∧ _ ∧ _ |- _ ] => destruct H as [[? [? [? [? ?]]]]]
  | [ H : ∃ _ _,  _ ∧ _ |- _ ] => destruct H as [? [? [? ?]]]
  | [ H : ∃ _ _, _ |- _ ] => destruct H as [? [? ?]]
  end.

Ltac exist_tree :=
  repeat match goal with
  | [ H : ?t ▷ ?A ={?G}=> ?w |- ∃ t1, t1 ▷ ?A ={?G}=> ?w ∧ _ ] =>
    exists t; split; [exact H|]; clear H
  end.

Lemma amb_encoding_sound {Σ N : Type} G `{!Acyclic G} (m : model Σ N) k :
  0 < k → amb_encoding G m k → ambiguous G.
Proof.
  (* intros Hgt [Hm [δ [A [Hk [HA [ψ1 [ψ2 [Hne [Hin1 [Hin2 [Hψ1 Hψ2]]]]]]]]]]].
  exists A, (decode m 0 δ).
  pose (ψ_witness _ _ _ _ _ _ Hm Hgt Hk HA Hin1 Hψ1) as H1.
  pose (ψ_witness _ _ _ _ _ _ Hm Hgt Hk HA Hin2 Hψ2) as H2.
  destruct ψ1; destruct ψ2; simpl in H1; simpl in H2; split_exist_and; exist_tree.
  all: simpl; try done. *)
Admitted.
*)

Definition multi_derive_encoding {Σ N : Type} (G : grammar Σ N) (m : model Σ N) (H : N) (x δ : nat) : Prop.
Admitted.

Lemma multi_derive_encoding_sound {Σ N} (G : grammar Σ N) m H x δ :
  multi_derive_encoding G m H x δ →
  ∃ t1 t2, t1 ▷ H ={G}=> decode m x δ ∧ t2 ▷ H ={G}=> decode m x δ ∧
    ¬ similar t1 t2.
Admitted.

(* Main theorem *)

Definition amb_encoding {Σ N : Type} (G : grammar Σ N) (m : model Σ N) (A : N) (k : nat) : Prop :=
  derive_encoding G m k ∧ reachable_encoding G m k ∧ ∃ H x δ, x + δ ≤ k ∧
    can_reach m A 0 k H x δ ∧ multi_derive_encoding G m H x δ.

Theorem amb_encoding_sound {Σ N} `{EqDecision N} `{EqDecision (token Σ)}
  (G : grammar Σ N) m A k :
  acyclic G →
  amb_encoding G m A k → derive_amb G A (decode m 0 k).
Proof.
  intros HG [? [? [H [x [δ [? [? ?]]]]]]].
  apply derive_amb_iff_local_amb.
  exists H, (decode m x δ).
  split. eapply reachable_encoding_sound; eauto.
  by apply multi_derive_encoding_sound.
Qed.
