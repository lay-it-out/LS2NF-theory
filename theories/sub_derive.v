From stdpp Require Import relations list.
From Coq Require Import ssreflect.
From ambig Require Import grammar util.

Section sub_derive.

  Variable Σ N : Type.
  Context `{EqDecision Σ}.
  Context `{EqDecision N}.

  Variable G : grammar Σ N.

  Implicit Type A B S : N.
  Implicit Type w v u : sentence Σ.

  (* subtree *)

  Inductive child : relation (tree Σ N) :=
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

  Definition subtree : relation (tree Σ N) := rtc child.

  (* By definition, subtree is transitive *)

  Lemma subtree_valid t t' :
    subtree t' t →
    ✓{G} t →
    ✓{G} t'.
  Proof.
    induction 1 => ? //.
    eapply child_valid; eauto.
  Qed.

  (* sub derivation *)

  Definition sig : Type := N * sentence Σ.

  Definition sub_derive : relation sig :=
    λ σ1 σ2, match σ1, σ2 with (A, w), (B, v) =>
      ∀ t', t' ▷ B ={G}=> v →
        ∃ t, t ▷ A ={G}=> w ∧ subtree t' t
    end.

  Global Instance sub_derive_trans : Transitive sub_derive.
  Proof.
    intros [A w] [B v] [C u] HAB HBC t Ht.
    specialize (HBC _ Ht) as [t1 [Ht1 ?]].
    specialize (HAB _ Ht1) as [t2 [Ht2 ?]].
    exists t2. split; [done | etrans; eauto].
  Qed.

  (* encoding sub derivation via sig reachable *)

  Inductive step : relation sig :=
  | step_unary A B φ w :
    A ↦ unary B φ ∈ G →
    apply₁ φ w = true →
    step (A, w) (B, w)
  | step_left A Bl Br φ wl wr :
    A ↦ binary Bl Br φ ∈ G →
    apply₂ φ wl wr = true →
    G ⊨ Br ⇒ wr →
    step (A, wl ++ wr) (Bl, wl)
  | step_right A Bl Br φ wl wr :
    A ↦ binary Bl Br φ ∈ G →
    apply₂ φ wl wr = true →
    G ⊨ Bl ⇒ wl →
    step (A, wl ++ wr) (Br, wr)
  .

  Infix "→₁" := step (at level 40).

  Definition reachable : relation sig := rtc step.

  Infix "→∗" := reachable (at level 40).

  Lemma step_spec A w B v :
    (A, w) →₁ (B, v) → sub_derive (A, w) (B, v).
  Proof.
    inversion 1; subst; intros t' [? [? ?]].
    - exists (unary_tree A t').
      split; last by apply rtc_once; constructor.
      repeat split. naive_solver. econstructor; naive_solver.
    - destruct H6 as [tr [? [? ?]]].
      exists (binary_tree A t' tr).
      split; last by apply rtc_once; constructor.
      repeat split. naive_solver. econstructor; naive_solver.
    - destruct H6 as [tl [? [? ?]]].
      exists (binary_tree A tl t').
      split; last by apply rtc_once; constructor.
      repeat split. naive_solver. econstructor; naive_solver.
  Qed.

  Lemma reachable_spec A w B v :
    G ⊨ B ⇒ v →
    (A, w) →∗ (B, v) ↔ sub_derive (A, w) (B, v).
  Proof.
    intros Hv. split.
    - (* -> *)
      induction 1 as [[]|[] [] []].
      + intros t ?. exists t. split; [done | constructor].
      + apply step_spec in H. etrans; eauto.
    - (* <- *)
      intros H. destruct Hv as [t' Ht'].
      specialize (H _ Ht') as [t [? Hsub]].
      generalize dependent w.
      generalize dependent A.
      induction t => A w [? [? Ht]].
      all: apply rtc_inv_r in Hsub as [->|[c [? Hc]]].
      all: try by (have [-> ->] : A = B ∧ v = w by
          destruct Ht' as [? [? ?]]; naive_solver); constructor.
      all: inversion Hc; subst; clear Hc.
      all: inversion Ht; subst; clear Ht.
      + econstructor. eapply step_unary; eauto.
        by apply IHt.
      + econstructor. eapply step_left; eauto.
        by exists t2. by apply IHt1.
      + econstructor. eapply step_right; eauto.
        by exists t1. by apply IHt2.
  Qed.

  Inductive reachable_to σ : sig → Prop :=
  | reachable_to_refl :
    reachable_to σ σ
  | reachable_to_unary A B w φ :
    A ↦ unary B φ ∈ G →
    reachable_to σ (B, w) →
    apply₁ φ w = true →
    reachable_to σ (A, w)
  | reachable_to_left A Bl w1 Br w2 φ :
    A ↦ binary Bl Br φ ∈ G →
    reachable_to σ (Bl, w1) →
    G ⊨ Br ⇒ w2 →
    apply₂ φ w1 w2 = true →
    reachable_to σ (A, w1 ++ w2)
  | reachable_to_right A Bl w1 Br w2 φ :
    A ↦ binary Bl Br φ ∈ G →
    reachable_to σ (Br, w2) →
    G ⊨ Bl ⇒ w1 →
    apply₂ φ w1 w2 = true →
    reachable_to σ (A, w1 ++ w2)
  .

  Lemma reachable_to_spec σ τ :
    reachable_to σ τ ↔ τ →∗ σ.
  Proof.
    split.
    - (* -> *)
      induction 1; subst. constructor.
      all: econstructor; last eauto.
      all: econstructor; eauto.
    - (* <- *)
      induction 1 as [|? ? ? Hst]; subst. constructor.
      all: inversion Hst; subst; clear Hst.
      + eapply reachable_to_unary; eauto.
      + eapply reachable_to_left; eauto.
      + eapply reachable_to_right; eauto.
  Qed.

  (* Inductive sub_derive_2 S u : N → sentence Σ → Prop :=
  | sub_derive_2_refl :
    G ⊨ S ⇒ u →
    sub_derive_2 S u S u
  | sub_derive_2_unary A B φ w :
    A ↦ unary B φ ∈ G →
    sub_derive_2 S u A w →
    apply₁ φ w = true →
    sub_derive_2 S u B w
  | sub_derive_2_left A Bl Br φ wl wr :
    A ↦ binary Bl Br φ ∈ G →
    sub_derive_2 S u A (wl ++ wr) →
    G ⊨ Br ⇒ wr →
    apply₂ φ wl wr = true →
    sub_derive_2 S u Bl wl
  | sub_derive_2_right A Bl Br φ wl wr :
    A ↦ binary Bl Br φ ∈ G →
    sub_derive_2 S u A (wl ++ wr) →
    G ⊨ Bl ⇒ wl →
    apply₂ φ wl wr = true →
    sub_derive_2 S u Br wr
  .

  Lemma sub_derive_2_spec A w B v :
    sub_derive_2 A w B v ↔ sub_derive A w B v.
  Proof.
    split.
    - (* -> *)
      induction 1; subst.
      + destruct H as [t ?].
        exists t, t.
        split; first done.
        split; first done.
        constructor.
      + have Ht : unary_tree A0 t' ▷ A0 ={ G }=> w0.
        { destruct Ht' as [? [? ?]].
          repeat split. naive_solver. econstructor; naive_solver. }
        specialize (IHsub_derive_2 _ Ht) as [t [? ?]].
        exists t. split; first done.
        etrans; last eauto. constructor; constructor.
      + destruct H1 as [tr [? [? ?]]].
        have Ht : binary_tree A0 t' tr ▷ A0 ={ G }=> (wl ++ wr).
        { destruct Ht' as [? [? ?]].
          repeat split. naive_solver. econstructor; naive_solver. }
        specialize (IHsub_derive_2 _ Ht) as [t [? ?]].
        exists t. split; first done.
        etrans; last eauto. constructor; constructor.
      + destruct H1 as [tl [? [? ?]]].
        have Ht : binary_tree A0 tl t' ▷ A0 ={ G }=> (wl ++ wr).
        { destruct Ht' as [? [? ?]].
          repeat split. naive_solver. econstructor; naive_solver. }
        specialize (IHsub_derive_2 _ Ht) as [t [? ?]].
        exists t. split; first done.
        etrans; last eauto. constructor; constructor.
    - (* <- *)
      have [t Ht] : G ⊨ B ⇒ v. admit.
      intros H. induction t.
      + admit.
      + admit.
      + destruct Ht as [? [? Ht]].
        inversion Ht; subst; clear Ht.
        eapply sub_derive_2_unary
      unfold sub_derive.
  *)

End sub_derive.

Arguments step {_} {_}.
Arguments reachable {_} {_}.
Arguments reachable_to {_} {_}.
