From stdpp Require Import vector relations.
From LS2NF Require Import grammar equiv_class.
From Coq Require Import ssreflect.

Section synthesis.

  Context {Σ N : Type}.
  Implicit Type t : @tree Σ N.
  Implicit Type w : sentence Σ.

  Open Scope grammar_scope.

  Inductive tree_iso : @tree Σ N → @tree Σ N → Prop :=
    | ε_tree_iso A : tree_iso (ε_tree A) (ε_tree A)
    | token_tree_iso A tk1 tk2 :
      token tk1 = token tk2 →
      tree_iso (token_tree A tk1) (token_tree A tk2)
    | unary_tree_iso A t1 t2 :
      tree_iso t1 t2 →
      tree_iso (unary_tree A t1) (unary_tree A t2)
    | binary_tree_iso A t1l t1r t2l t2r :
      tree_iso t1l t2l →
      tree_iso t1r t2r →
      tree_iso (binary_tree A t1l t1r) (binary_tree A t2l t2r)
    .

  Global Instance tree_equiv : Equiv (@tree Σ N) := tree_iso.

  (* tree_iso is an equivalent relation *)

  Global Instance tree_iso_refl : Reflexive tree_iso.
  Proof.
    intros t. induction t.
    - apply ε_tree_iso.
    - by apply token_tree_iso.
    - by apply unary_tree_iso.
    - by apply binary_tree_iso.
  Qed.

  Global Instance tree_iso_sym : Symmetric tree_iso.
  Proof.
    intros t1 t2. induction 1.
    - apply ε_tree_iso.
    - by apply token_tree_iso.
    - by apply unary_tree_iso.
    - by apply binary_tree_iso.
  Qed.

  Global Instance tree_iso_trans : Transitive tree_iso.
  Proof.
    intros t1 t2 t H1.
    revert t. induction H1; inversion 1; subst.
    - apply ε_tree_iso.
    - apply token_tree_iso; congruence.
    - apply unary_tree_iso. naive_solver.
    - apply binary_tree_iso; naive_solver.
  Qed.

  Global Instance tree_iso_equiv : Equivalence tree_iso := {
    Equivalence_Reflexive := tree_iso_refl;
    Equivalence_Symmetric := tree_iso_sym;
    Equivalence_Transitive := tree_iso_trans;
  }.

  Lemma trees_iso_word_length_eq t1 t2 :
    t1 ≡ t2 →
    length (word t1) = length (word t2).
  Proof.
    induction 1 => //=. rewrite !app_length. naive_solver.
  Qed.

  Lemma trees_iso_same_word_eq t1 t2 :
    t1 ≡ t2 →
    word t1 = word t2 →
    t1 = t2.
  Proof.
    induction 1 => //=. 1,2: naive_solver.
    intros Heq. apply app_inj_1 in Heq; last by apply trees_iso_word_length_eq.
    naive_solver.
  Qed.

  Context (G : grammar Σ N).
  Context (A : N).

  Definition sentence_iso w1 w2 : Prop :=
    (∀ t1, t1 ▷ A ={ G }=> w1 → ∃ t2, t2 ▷ A ={ G }=> w2 ∧ tree_iso t1 t2) ∧
    (∀ t2, t2 ▷ A ={ G }=> w2 → ∃ t1, t1 ▷ A ={ G }=> w1 ∧ tree_iso t1 t2).

  (* sentence_iso is also an equivalent relation *)

  Global Instance sentence_iso_refl : Reflexive sentence_iso.
  Proof.
    intros w. split => t Ht; exists t; naive_solver.
  Qed.

  Global Instance sentence_iso_sym : Symmetric sentence_iso.
  Proof.
    intros w1 w2 [H1 H2]. split => t Ht.
    - destruct (H2 _ Ht) as [t' Ht']. exists t'. naive_solver.
    - destruct (H1 _ Ht) as [t' Ht']. exists t'. naive_solver.
  Qed.

  Global Instance sentence_iso_trans : Transitive sentence_iso.
  Proof.
    intros w1 w2 w3 [H12 H21] [H23 H32]. split => t Ht.
    - destruct (H12 _ Ht) as [t1 [Ht1 ?]]. destruct (H23 _ Ht1) as [t2 [? ?]].
      exists t2. split; first naive_solver. etrans; eauto.
    - destruct (H32 _ Ht) as [t1 [Ht1 ?]]. destruct (H21 _ Ht1) as [t2 [? ?]].
      exists t2. split; first naive_solver. etrans; eauto.
  Qed.

  Global Instance sentence_iso_equiv : Equivalence sentence_iso := {
    Equivalence_Reflexive := sentence_iso_refl;
    Equivalence_Symmetric := sentence_iso_sym;
    Equivalence_Transitive := sentence_iso_trans;
  }.

  (* Synthesis conditions: G is the refined grammar we need to solve. *)

  Definition acceptance n (W : vec (sentence Σ) n) (T : vec (@tree Σ N) n) : Prop :=
    ∀ i, T !!! i ▷ A ={ G }=> W !!! i.

  Fixpoint fill_tree t (ps : list (nat * nat)) :=
    match t with
    | ε_tree A => (ε_tree A, ps)
    | token_tree A tk =>
      match ps with
      | [] => (token_tree A tk, [])
      | p :: ps' => (token_tree A (token tk @ p), ps')
      end
    | unary_tree A t =>
      let (t', ps') := fill_tree t ps in
      (unary_tree A t', ps')
    | binary_tree A t1 t2 =>
      let (t1', ps1) := fill_tree t1 ps in
      let (t2', ps2) := fill_tree t2 ps1 in
      (binary_tree A t1' t2', ps2)
    end.

  Definition reformat_tree t w := (fill_tree t (pos <$> w)).1.

  Local Lemma destruct_pair_lemma {α β : Type} (p : α * β) a b :
    p = (a, b) → p.1 = a ∧ p.2 = b.
  Proof. naive_solver. Qed.

  Local Ltac destruct_pair :=
    repeat match goal with
    | [ H : _ = (_, _) |- _ ] => apply destruct_pair_lemma in H
    end.

  Lemma fill_tree_iso t l :
    (fill_tree t l).1 ≡ t.
  Proof.
    generalize dependent l.
    induction t => l /=; repeat case_match; destruct_pair; simplify_eq/=.
    - apply ε_tree_iso.
    - by apply token_tree_iso.
    - by apply token_tree_iso.
    - apply unary_tree_iso. naive_solver.
    - apply binary_tree_iso; naive_solver.
  Qed.

  Corollary reformat_tree_iso t w :
    reformat_tree t w ≡ t.
  Proof. by apply fill_tree_iso. Qed.

  Lemma reformat_tree_word t w :
    token <$> word t = token <$> w →
    word (reformat_tree t w) = w.
  Proof.
    induction t => //=.
  Admitted.

  Definition rejection n (W : vec (sentence Σ) n) (T : vec (@tree Σ N) n) : Prop :=
    ∀ i j, i ≠ j → ¬ (reformat_tree (T !!! j) (W !!! i) ▷ A ={ G }=> W !!! i).

  Definition synthesis_conditions n W T : Prop :=
    acceptance n W T ∧ rejection n W T.

  Definition valid n (W : vec (sentence Σ) n) : Prop :=
    ∀ i j, token <$> W !!! i = token <$> W !!! j.

  Lemma tree_not_iso_with_rejected n W T :
    valid n W →
    synthesis_conditions n W T →
    ∀ i t, t ▷ A ={ G }=> W !!! i → ∀ j, j ≠ i → t ≢ T !!! j.
  Proof.
    intros ? [Hacc Hrej] i t Ht j ? Hyp.
    eapply Hrej with (i := i); eauto.
    have -> : reformat_tree (T !!! j) (W !!! i) = t.
    { eapply trees_iso_same_word_eq.
      - etrans. 2: symmetry; eauto. by apply reformat_tree_iso.
      - rewrite reformat_tree_word //. 1: by destruct (Hacc j) as [_ [-> _]].
        by destruct Ht as [? [? ?]]. }
    done.
  Qed.

  Definition sentence_equiv_class := @equiv_class (sentence Σ) sentence_iso.

  Theorem synthesis_conditions_imply_equiv_class_disjoint n W T :
    valid n W →
    synthesis_conditions n W T →
    ∀ i j l k, i ≠ j →
      sentence_equiv_class (W !!! i) l →
      sentence_equiv_class (W !!! j) k →
      l ## k.
  Proof.
    intros ? Hc i j l k ? ? ?.
    eapply equiv_class_disjoint; eauto. intros [Hi ?].
    have [Hacc _] := Hc.
    destruct (Hi _ (Hacc i)) as [t [Ht ?]].
    eapply tree_not_iso_with_rejected in Hc. 3: apply Ht. all: eauto.
    apply Hc. by symmetry.
  Qed.

End synthesis.