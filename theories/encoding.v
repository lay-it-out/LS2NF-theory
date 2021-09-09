From stdpp Require Import relations.
From Coq Require Import ssreflect.
From ambig Require Import grammar ambiguity.

(* sat model *)

Record model (Σ N : Type) := {
  token : nat → Σ;
  line : nat → nat;
  col : nat → nat;
  can_derive : N → nat (* start (inclusive) *) → nat (* delta = end (inclusive) - start *) → bool;
}.

Arguments token {_} {_}.
Arguments line {_} {_}.
Arguments col {_} {_}.
Arguments can_derive {_} {_}.

Fixpoint decode {Σ N : Type} (m : model Σ N) (x δ : nat) : sentence Σ :=
  token m x @ (line m x, col m x) ::
    match δ with
    | 0 => []
    | S n => decode m (S x) n
    end.

Lemma decode_merge {Σ N : Type} (m : model Σ N) x δ δ' :
  δ' < δ →
  decode m x δ' ++ decode m (x + δ' + 1) (δ - δ' - 1) = decode m x δ.
(* Proof.
  intros.
  generalize dependent x.
  induction δ as [|n IHn]; first lia.
  induction δ' as [|n' IHn']; intros x.
  - simpl.
    have -> : x + 0 + 1 = S x by lia.
    have -> : n - 0 = n by lia.
    done.
  - simpl.
    rewrite -IHn. *)
Admitted.

(* encoding membership *)

Definition φ_atom {Σ N : Type} (G : grammar Σ N) (A : N) (x δ : nat) (m : model Σ N) : Prop :=
  δ = 0 ∧ ∃ a, G ⊢ A ↦ atom a ∧ token m x = a.

Definition φ_unary {Σ N : Type} (G : grammar Σ N) (A : N) x δ (m : model Σ N) : Prop :=
  ∃ B φ, G ⊢ A ↦ unary B φ ∧ can_derive m B x δ = true ∧ φ (decode m x δ).

Definition φ_binary_null_l {Σ N : Type} (G : grammar Σ N) (A : N) (x δ : nat) (m : model Σ N) : Prop :=
  ∃ E B φ, G ⊢ A ↦ binary E B φ ∧ nullable G E = true ∧ can_derive m B x δ = true.

Definition φ_binary_null_r {Σ N : Type} (G : grammar Σ N) (A : N) (x δ : nat) (m : model Σ N) : Prop :=
  ∃ B E φ, G ⊢ A ↦ binary B E φ ∧ nullable G E = true ∧ can_derive m B x δ = true.

Definition φ_binary {Σ N : Type} (G : grammar Σ N) (A : N) (x δ : nat) (m : model Σ N) : Prop :=
  δ > 0 ∧ ∃ δ' B1 B2 φ, δ' < δ ∧ G ⊢ A ↦ binary B1 B2 φ ∧
    can_derive m B1 x δ' = true ∧
    can_derive m B2 (x + δ' + 1) (δ - δ' - 1) = true ∧
    φ (decode m x δ') (decode m (x + δ' + 1) (δ - δ' - 1)).

Definition membership_formula {Σ N : Type} (G : grammar Σ N) (m : model Σ N) (k : nat) : Prop :=
  ∀ x δ, x + δ < k → ∀ A,
    can_derive m A x δ = true →
    φ_atom G A x δ m ∨ φ_unary G A x δ m ∨
    φ_binary_null_l G A x δ m ∨ φ_binary_null_r G A x δ m ∨
    φ_binary G A x δ m.

Lemma encode_sound_aux {Σ N : Type} G `{!Acyclic G} (m : model Σ N) (A : N) B x δ :
  A ⇒{G} B →
  can_derive m B x δ = true →
  G ⊨ B ⇒ decode m x δ.
Proof.
  induction A as [A IHA] using (well_founded_induction N_lt_wf).
  intros. apply (IHA B); last done.
  - by apply acyclic.
  - by apply derive_nonterm_refl.
Qed.

Lemma encode_sound {Σ N : Type} G `{!Acyclic G} (m : model Σ N) k :
  membership_formula G m k →
  ∀ x δ, x + δ < k → ∀ A,
    can_derive m A x δ = true → G ⊨ A ⇒ decode m x δ.
Proof.
  intros Hf x δ Hk.
  generalize dependent x.
  induction δ as [δ IHδ] using lt_wf_ind.
  intros x Hk A HA.
  specialize (Hf _ _ Hk _ HA).
  repeat destruct Hf as [Hf | Hf].
  - destruct Hf as [-> [a [HP Ha]]].
    apply derive_atom. by rewrite Ha.
  - clear IHδ.
    destruct Hf as [B [φ [HP [HB Hφ]]]].
    eapply derive_unary; eauto.
    apply @encode_sound_aux with (A := A).
    2: eapply derive_nonterm_unary; eauto.
    all: done.
  - clear IHδ.
    destruct Hf as [E [B [φ [HP [HE HB]]]]].
    eapply binary_nullable_l; eauto.
    apply @encode_sound_aux with (A := A).
    2: eapply derive_nonterm_binary_nullable_l; eauto.
    all: done.
  - clear IHδ.
    destruct Hf as [B [E [φ [HP [HE HB]]]]].
    eapply binary_nullable_r; eauto.
    apply @encode_sound_aux with (A := A).
    2: eapply derive_nonterm_binary_nullable_r; eauto.
    all: done.
  - destruct Hf as [Hδ [δ' [B1 [B2 [φ [Hδ' [HP [HB1 [HB2 Hφ]]]]]]]]].
    erewrite <- decode_merge; last eauto.
    eapply derive_binary; eauto.
    all: apply IHδ; auto; lia.
Qed.

(* encoding ambiguity *)

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
  | ψ_atom a => δ = 0 ∧ token m 0 = a
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
  | ψ_atom a => ∃ tk, w = [tk] ∧ (token_tree A tk) ▷ A ={G}=> w
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
    exists (token m 0 @ (line m 0, col m 0)).
    split; first done.
    apply token_tree_witness. congruence.
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
  0 < k → amb_encoding G m k → bounded_ambiguous G.
Proof.
  intros Hgt [Hm [δ [A [Hk [HA [ψ1 [ψ2 [Hne [Hin1 [Hin2 [Hψ1 Hψ2]]]]]]]]]]].
  exists A, (decode m 0 δ).
  pose (ψ_witness _ _ _ _ _ _ Hm Hgt Hk HA Hin1 Hψ1) as H1.
  pose (ψ_witness _ _ _ _ _ _ Hm Hgt Hk HA Hin2 Hψ2) as H2.
  destruct ψ1; destruct ψ2; simpl in H1; simpl in H2; split_exist_and; exist_tree.
  all: simpl; try done.
  (* TODO : for every ψ1, ψ2 ∈ ψ_intro G A, nonterminals at first level must differ *)
Admitted.
