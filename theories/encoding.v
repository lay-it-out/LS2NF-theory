From stdpp Require Import relations.
From Coq Require Import ssreflect.
From ambig Require Import grammar acyclic reachable ambiguity.

(* sat model *)

Record model (Σ N : Type) := {
  term : nat → Σ;
  line : nat → nat;
  col : nat → nat;
  can_derive : N → nat (* start (inclusive) *) → nat (* length *) → bool;
  can_reach : N → nat (* start (inclusive) *) → nat (* length *) → N → nat → nat → bool;
}.

Arguments term {_} {_}.
Arguments line {_} {_}.
Arguments col {_} {_}.
Arguments can_derive {_} {_}.
Arguments can_reach {_} {_}.

Fixpoint decode {Σ N : Type} (m : model Σ N) (x δ : nat) : sentence Σ :=
  match δ with
  | 0 => []
  | S n => term m x @ (line m x, col m x) :: decode m (S x) n
  end.

Lemma decode_length {Σ N : Type} (m : model Σ N) x δ :
  length (decode m x δ) = δ.
Proof.
  generalize dependent x.
  induction δ => x //=.
  naive_solver.
Qed.

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
    (δ = 1 ∧ ∃ a, A ↦ atom a ∈ G ∧ term m x = a) ∨
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
    (∃ B φ, A ↦ unary B φ ∈ G ∧ can_reach m B x δ H xH δH ∧ φ (decode m x δ)) ∨
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

(* encoding multiple derivation *)

Definition binary_can_derive {Σ N : Type} (m : model Σ N) (A B : N) φ (x δ δ' : nat) : Prop :=
  can_derive m A x δ' ∧ can_derive m B (x + δ') (δ - δ') ∧
    φ (decode m x δ') (decode m (x + δ') (δ - δ')).

Lemma binary_can_derive_witness {Σ N} (G : grammar Σ N) m A Bl Br φ x δ δ' k :
  acyclic G →
  derive_encoding G m k →
  x + δ ≤ k →
  δ' ≤ δ →
  A ↦ binary Bl Br φ ∈ G →
  binary_can_derive m Bl Br φ x δ δ' →
  ∃ t1 t2, root t1 = Bl ∧ root t2 = Br ∧ word t1 = decode m x δ' ∧
    (binary_tree A t1 t2) ▷ A ={G}=> decode m x δ.
Proof.
  intros HG ? ? ? ? [Hdl [Hdr ?]].
  eapply derive_encoding_sound in Hdl as [t1 [? [? ?]]]; [eauto..|lia].
  eapply derive_encoding_sound in Hdr as [t2 [? [? ?]]]; [eauto..|lia].
  exists t1, t2. repeat split => //.
  have ? : decode m x δ' ++ decode m (x + δ') (δ - δ') = decode m x δ.
  { rewrite decode_merge. by have -> : δ' + (δ - δ') = δ by lia. }
  repeat split. simpl in *. congruence.
  eapply valid_binary_tree; eauto. naive_solver. congruence.
Qed.

Definition clause_can_derive {Σ N : Type} (m : model Σ N) (α : clause Σ N) (x δ : nat) :=
  match α with
  | ε => δ = 0
  | atom a => δ = 1 ∧ term m x = a
  | unary A φ => can_derive m A x δ ∧ φ (decode m x δ)
  | binary A B φ => ∃ δ', δ' ≤ δ ∧ binary_can_derive m A B φ x δ δ'
  end.

Lemma clause_can_derive_witness {Σ N} (G : grammar Σ N) m A α x δ k :
  acyclic G →
  derive_encoding G m k →
  x + δ ≤ k →
  A ↦ α ∈ G →
  clause_can_derive m α x δ →
  match α with
  | ε => δ = 0 ∧ ε_tree A ▷ A ={G}=> decode m x δ
  | atom a => δ = 1 ∧ term m x = a ∧ (token_tree A (a @ (line m x, col m x))) ▷ A ={G}=> decode m x δ
  | unary B φ => ∃ t, root t = B ∧ (unary_tree A t) ▷ A ={G}=> decode m x δ
  | binary Bl Br φ => ∃ t1 t2, root t1 = Bl ∧ root t2 = Br ∧ 
    (binary_tree A t1 t2) ▷ A ={G}=> decode m x δ
  end.
Proof.
  intros HG ? ? ? Hd.
  destruct α; simpl in Hd.
  - split; first done. repeat split. naive_solver.
    by apply valid_ε_tree.
  - destruct Hd as [? ?].
    do 2 (split; first done). repeat split. naive_solver.
    by apply valid_token_tree.
  - destruct Hd as [Hd ?].
    eapply derive_encoding_sound in Hd as [t [? [? ?]]]; eauto.
    exists t. split; first done. repeat split => //.
    eapply valid_unary_tree; eauto. naive_solver. congruence.
  - destruct Hd as [δ' [? Hb]].
    eapply binary_can_derive_witness in Hb; eauto.
    naive_solver.
Qed.

Definition multi_derive_encoding {Σ N : Type} (G : grammar Σ N) (m : model Σ N) (H : N) (x δ : nat) : Prop :=
  (∃ α β, H ↦ α ∈ G ∧ H ↦ β ∈ G ∧ α ≠ β ∧
    clause_can_derive m α x δ ∧ clause_can_derive m β x δ) ∨
  (∃ A B φ δ₁ δ₂, H ↦ binary A B φ ∈ G ∧ δ₁ ≤ δ ∧ δ₂ ≤ δ ∧ δ₁ ≠ δ₂ ∧
    binary_can_derive m A B φ x δ δ₁ ∧ binary_can_derive m A B φ x δ δ₂).

Ltac split_exist_and :=
  repeat match goal with
  | [ H : _ ∧ _ |- _ ] => destruct H as [? ?]
  | [ H : ∃ _, _ ∧ _ ∧ _ |- _ ] => destruct H as [? [? [? ?]]]
  | [ H : ∃ _, _ ∧ _ |- _ ] => destruct H as [? [? ?]]
  | [ H : ∃ _, _ |- _ ] => destruct H as [? ?]
  | [ H : ∃ _ _, _ ∧ _ ∧ _ |- _ ] => destruct H as [[? [? [? [? ?]]]]]
  | [ H : ∃ _ _,  _ ∧ _ |- _ ] => destruct H as [? [? [? ?]]]
  | [ H : ∃ _ _, _ |- _ ] => destruct H as [? [? ?]]
  end.

Lemma multi_derive_encoding_sound {Σ N} (G : grammar Σ N) m k H x δ :
  acyclic G →
  derive_encoding G m k →
  x + δ ≤ k →
  multi_derive_encoding G m H x δ →
  ∃ t1 t2, t1 ▷ H ={G}=> decode m x δ ∧ t2 ▷ H ={G}=> decode m x δ ∧
    ¬ similar t1 t2.
Proof.
  intros HG Hd Hk Hf.
  destruct Hf as [Hf | Hf].
  - destruct Hf as [α [β [? [? [Hne [Hα Hβ]]]]]].
    eapply clause_can_derive_witness in Hα; eauto.
    eapply clause_can_derive_witness in Hβ; eauto.
    destruct α; destruct β.
    all: split_exist_and.
    all: try congruence.
    all: eexists; eexists.
    all: repeat match goal with
    | [ H : ?t ▷ ?A ={?G}=> ?w |- _ ▷ ?A ={?G}=> ?w ∧ _ ] =>
    split; [by exact H|]; clear H
    end.
    all: try done.
    + simpl in *; subst. intros Heq. rewrite Heq in H1. apply Hne.
      rewrite Heq. f_equal.
      eapply unary_predicate_unique; eauto.
    + simpl in *; subst. intros [Heq1 [Heq2 ?]].
      rewrite Heq1 Heq2 in H1. apply Hne.
      rewrite Heq1 Heq2. f_equal.
      eapply binary_predicate_unique; eauto.
  - destruct Hf as [A [B [φ [δ₁ [δ₂ [? [? [? [? [H1 H2]]]]]]]]]].
    eapply binary_can_derive_witness in H1 as [t1l [t1r [_ [_ [Hw1 Ht1]]]]]; eauto.
    eapply binary_can_derive_witness in H2 as [t2l [t2r [_ [_ [Hw2 Ht2]]]]]; eauto.
    do 2 eexists. split; first by apply Ht1. split; first by apply Ht2.
    have ? : word t1l ≠ word t2l.
    { rewrite Hw1 Hw2. intros ?.
      have : length (decode m x δ₁) = length (decode m x δ₂) by congruence.
      by rewrite !decode_length. }
    naive_solver.
Qed.

(* Main theorem *)

Definition amb_encoding {Σ N : Type} (G : grammar Σ N) (m : model Σ N) (A : N) (k : nat) : Prop :=
  derive_encoding G m k ∧ reachable_encoding G m k ∧ ∃ H x δ, x + δ ≤ k ∧
    can_reach m A 0 k H x δ ∧ multi_derive_encoding G m H x δ.

Theorem amb_encoding_sound {Σ N} `{EqDecision N} `{EqDecision (token Σ)}
  (G : grammar Σ N) A k :
  acyclic G →
  (∃ m, amb_encoding G m A k) → 
  ∃ w, length w = k ∧ derive_amb G A w.
Proof.
  intros HG [m [? [? [H [x [δ [? [? ?]]]]]]]].
  exists (decode m 0 k). split; first by rewrite decode_length.
  apply derive_amb_iff_local_amb.
  exists H, (decode m x δ).
  split. eapply reachable_encoding_sound; eauto.
  eapply multi_derive_encoding_sound; eauto.
Qed.

(* TODO *)
Definition amb_encoding_complete {Σ N} `{EqDecision N} `{EqDecision (token Σ)}
  (G : grammar Σ N) A k :=
  acyclic G →
  (∃ w, length w = k ∧ derive_amb G A w) →
  ∃ m, amb_encoding G m A k.
