From stdpp Require Import relations list.
From Coq Require Import ssreflect.
From LS2NF Require Import grammar util slice.

Section sub_derive.

  (** * Preliminary: Subtree Relation *)

  Context {Σ N : Type} `{!EqDecision Σ} `{!EqDecision N}.
  Context (G : grammar Σ N).

  Implicit Type A B S : N.
  Implicit Type w v u : sentence Σ.

  Open Scope grammar_scope.

  (** Child relation: [child t1 t2] indicates that tree [t1] is a child of [t2]. *)
  Inductive child : relation (@tree Σ N) :=
  | child_unary A t :
    child t (unary_tree A t)
  | child_left A t t' :
    child t (binary_tree A t t')
  | child_right A t t' :
    child t (binary_tree A t' t)
  .

  Lemma child_valid t t' :
    child t' t →
    ✓{G} t →
    ✓{G} t'.
  Proof.
    induction 1; inversion 1; subst.
    all: naive_solver.
  Qed.

  (** Subtree relation: [subtree t1 t2] indicates that tree [t1] is a subtree of [t2], which is 
      indeed the reflexive transitive closure of [child]. *)
  Definition subtree := rtc child.

  (** Tree validity is reserved under [subtree] relation. *)
  Lemma subtree_valid t t' :
    subtree t' t →
    ✓{G} t →
    ✓{G} t'.
  Proof.
    induction 1 => ? //.
    eapply child_valid; eauto.
  Qed.

  (** Inversion lemmas about [subtree]. *)

  Lemma subtree_ε_inv t A :
    subtree t (ε_tree A) → t = ε_tree A.
  Proof.
    intros H. apply rtc_inv_r in H.
    destruct H as [|[T [? Hc]]]; first done.
    by inversion Hc.
  Qed.

  Lemma subtree_token_inv t A tk :
    subtree t (token_tree A tk) → t = token_tree A tk.
  Proof.
    intros H. apply rtc_inv_r in H.
    destruct H as [|[T [? Hc]]]; first done.
    by inversion Hc.
  Qed.

  Lemma subtree_unary_inv t' A t :
    subtree t' (unary_tree A t) → t' = unary_tree A t ∨ subtree t' t.
  Proof.
    intros H. apply rtc_inv_r in H.
    destruct H as [|[T [? Hc]]]; [by left | right].
    invert Hc. done.
  Qed.

  Lemma subtree_binary_inv t' A tl tr :
    subtree t' (binary_tree A tl tr) →
    t' = binary_tree A tl tr ∨ subtree t' tl ∨ subtree t' tr.
  Proof.
    intros H. apply rtc_inv_r in H.
    destruct H as [|[T [? Hc]]]; [by left | right].
    invert Hc.
    all: naive_solver.
  Qed.

  (** * Sub-Derivation Relation *)

  (** A _signature_ is a pair of a nonterminal equipped with a sentence. *)
  Definition sig : Type := N * sentence Σ.

  (** Sub-derivation relation [sub_derive] (Definition 4.1). *)
  Definition sub_derive : relation sig :=
    λ σ1 σ2, match σ1, σ2 with (A, w), (B, v) =>
      ∀ t', t' ▷ B ={G}=> v →
        ∃ t, t ▷ A ={G}=> w ∧ subtree t' t
    end.

  (** [sub_derive] is transitive. *)
  Global Instance sub_derive_trans : Transitive sub_derive.
  Proof.
    intros [A w] [B v] [C u] HAB HBC t Ht.
    specialize (HBC _ Ht) as [t1 [Ht1 ?]].
    specialize (HAB _ Ht1) as [t2 [Ht2 ?]].
    exists t2. split; [done | etrans; eauto].
  Qed.

  (** * Reachability Relation *)

  (** One-step reachability relation [→₁] used in Definition 4.2. *)
  Inductive step : relation sig :=
  | step_unary A B φ w :
    A ↦ unary B φ ∈ G →
    app₁ φ w = true →
    step (A, w) (B, w)
  | step_left A Bl Br φ wl wr :
    A ↦ binary Bl Br φ ∈ G →
    app₂ φ wl wr = true →
    G ⊨ Br => wr →
    step (A, wl ++ wr) (Bl, wl)
  | step_right A Bl Br φ wl wr :
    A ↦ binary Bl Br φ ∈ G →
    app₂ φ wl wr = true →
    G ⊨ Bl => wl →
    step (A, wl ++ wr) (Br, wr)
  .

  Infix "→₁" := step (at level 40).

  (** Reachability relation [→∗] (Definition 4.2): reflexive transitive closure of [→₁]. *)
  Definition reachable : relation sig := rtc step.

  Infix "→∗" := reachable (at level 40).

  Lemma step_spec A w B v :
    (A, w) →₁ (B, v) → sub_derive (A, w) (B, v).
  Proof.
    inversion 1; subst; intros t' [? [? ?]].
    all: repeat match goal with
    | H : _ ⊨ _ => _ |- _ => destruct H as [? [? [? ?]]]
    end.
    - exists (unary_tree A t'). split.
      * repeat split. { naive_solver. } econstructor; naive_solver.
      * apply rtc_once. constructor.
    - eexists (binary_tree A t' _). split.
      * repeat split. { naive_solver. } econstructor; naive_solver.
      * apply rtc_once. constructor.
    - eexists (binary_tree A _ t'). split.
      * repeat split. { naive_solver. } econstructor; naive_solver.
      * apply rtc_once. constructor.
  Qed.

  (** The relationship between [→∗] and [sub_derive] (Lemma 4.3). *)
  Lemma reachable_spec A w B v :
    G ⊨ B => v →
    (A, w) →∗ (B, v) ↔ sub_derive (A, w) (B, v).
  Proof.
    intros Hv. split.
    - (* -> *)
      induction 1 as [[]|[] [] [] H1 ? ?].
      + intros t ?. exists t. split; [done | constructor].
      + apply step_spec in H1. etrans; eauto.
    - (* <- *)
      intros H. destruct Hv as [t' Ht'].
      specialize (H _ Ht') as [t [? Hsub]].
      generalize dependent w.
      generalize dependent A.
      induction t as [?|??|?? IHt|?? IHt1 ? IHt2] => A w [? [? Ht]].
      all: apply rtc_inv_r in Hsub as [->|[c [? Hc]]].
      all: try by (have [-> ->] : A = B ∧ v = w by
          destruct Ht' as [? [? ?]]; naive_solver); constructor.
      all: invert Hc.
      all: invert Ht.
      + econstructor. eapply step_unary; eauto. by apply IHt.
      + econstructor. eapply step_left; eauto.
        { by eexists. } by apply IHt1.
      + econstructor. eapply step_right; eauto.
        { by eexists. } by apply IHt2.
  Qed.

  Lemma step_sub A w B v :
    (A, w) →₁ (B, v) →
    ∃ vl vr, w = vl ++ v ++ vr.
  Proof.
    inversion 1; subst.
    - exists [], []. by rewrite app_nil_l app_nil_r.
    - exists [], wr. by rewrite app_nil_l.
    - exists wl, []. by rewrite app_nil_r.
  Qed.

  Lemma reachable_sub_sig σ τ :
    σ →∗ τ →
    ∃ vl vr, σ.2 = vl ++ τ.2 ++ vr.
  Proof.
    induction 1 as [[A w]|[A w] [B u] [C v] Hst ? IHst].
    - exists [], []. by rewrite app_nil_l app_nil_r.
    - simpl in *.
      apply step_sub in Hst as [v1 [v4 ->]].
      destruct IHst as [v2 [v3 ->]].
      exists (v1 ++ v2), (v3 ++ v4).
      by normalize_app_assoc.
  Qed.

  Lemma reachable_sublist A w B v :
    (A, w) →∗ (B, v) → sublist v w.
  Proof.
    apply reachable_sub_sig.
  Qed.

  (** A specialization of [σ₁ →∗ σ₂] when the target [σ₂] is fixed. *)
  Inductive reachable_to σ : sig → Prop :=
  | reachable_to_refl :
    reachable_to σ σ
  | reachable_to_unary A B w φ :
    A ↦ unary B φ ∈ G →
    reachable_to σ (B, w) →
    app₁ φ w = true →
    reachable_to σ (A, w)
  | reachable_to_left A Bl w1 Br w2 φ :
    A ↦ binary Bl Br φ ∈ G →
    reachable_to σ (Bl, w1) →
    G ⊨ Br => w2 →
    app₂ φ w1 w2 = true →
    reachable_to σ (A, w1 ++ w2)
  | reachable_to_right A Bl w1 Br w2 φ :
    A ↦ binary Bl Br φ ∈ G →
    reachable_to σ (Br, w2) →
    G ⊨ Bl => w1 →
    app₂ φ w1 w2 = true →
    reachable_to σ (A, w1 ++ w2)
  .

  Lemma reachable_to_spec σ τ :
    reachable_to τ σ ↔ σ →∗ τ.
  Proof.
    split.
    - (* -> *)
      induction 1; subst. constructor.
      all: econstructor; last eauto.
      all: econstructor; eauto.
    - (* <- *)
      apply rtc_ind_l. constructor.
      intros [] [] Hst ? ?.
      invert Hst.
      + eapply reachable_to_unary; eauto.
      + eapply reachable_to_left; eauto.
      + eapply reachable_to_right; eauto.
  Qed.

  (** A specialization of [σ₁ →∗ σ₂] when the source [σ₁] is fixed. *)
  Inductive reachable_from σ : sig → Prop :=
  | reachable_from_refl :
    reachable_from σ σ
  | reachable_from_unary A B w φ :
    A ↦ unary B φ ∈ G →
    reachable_from σ (A, w) →
    app₁ φ w = true →
    reachable_from σ (B, w)
  | reachable_from_left A Bl w1 Br w2 φ :
    A ↦ binary Bl Br φ ∈ G →
    reachable_from σ (A, w1 ++ w2) →
    G ⊨ Br => w2 →
    app₂ φ w1 w2 = true →
    reachable_from σ (Bl, w1)
  | reachable_from_right A Bl w1 Br w2 φ :
    A ↦ binary Bl Br φ ∈ G →
    reachable_from σ (A, w1 ++ w2) →
    G ⊨ Bl => w1 →
    app₂ φ w1 w2 = true →
    reachable_from σ (Br, w2)
  .

  Lemma reachable_from_spec σ τ :
    reachable_from σ τ ↔ σ →∗ τ.
  Proof.
    split.
    - (* -> *)
      induction 1; subst. constructor.
      all: eapply rtc_r; first eauto.
      all: econstructor; eauto.
    - (* <- *)
      apply rtc_ind_r. constructor.
      intros [] [] ? Hst ?.
      invert Hst.
      + eapply reachable_from_unary; eauto.
      + eapply reachable_from_left; eauto.
      + eapply reachable_from_right; eauto.
  Qed.

  Definition check_reachable_from σ τ : Prop :=
    match σ, τ with
    | (X, u), (B, w) =>
      (B = X ∧ w = u) ∨
      (∃ A φ, A ↦ unary B φ ∈ G ∧ reachable_from σ (A, w) ∧ app₁ φ w = true) ∨
      (∃ A B' φ w', A ↦ binary B B' φ ∈ G ∧ reachable_from σ (A, w ++ w') ∧ G ⊨ B' => w' ∧
        app₂ φ w w' = true) ∨
      (∃ A B' φ w', A ↦ binary B' B φ ∈ G ∧ reachable_from σ (A, w' ++ w) ∧ G ⊨ B' => w' ∧
        app₂ φ w' w = true)
    end.

  Lemma check_reachable_from_spec σ τ :
    check_reachable_from σ τ ↔ reachable_from σ τ.
  Proof.
    destruct σ as [X u].
    destruct τ as [B w].
    split.
    - intros [H|[H|[H|H]]].
      + destruct H as [-> ->]. apply reachable_from_refl.
      + destruct H as [A [φ [? [? ?]]]]. eapply reachable_from_unary; eauto.
      + destruct H as [A [B' [φ [w' [? [? [? ?]]]]]]]. eapply reachable_from_left; eauto.
      + destruct H as [A [B' [φ [w' [? [? [? ?]]]]]]]. eapply reachable_from_right; eauto.
    - inversion 1; subst.
      + by left.
      + right; left. naive_solver.
      + right; right; left. naive_solver.
      + right; right; right. naive_solver.
  Qed.

End sub_derive.

Arguments subtree {_} {_}.
Arguments sub_derive {_} {_}.

Arguments step {_} {_}.
Arguments reachable {_} {_}.
Arguments reachable_to {_} {_}.
Arguments reachable_from {_} {_}.
Arguments check_reachable_from {_} {_}.
