From stdpp Require Import vector relations.
From LS2NF Require Import grammar ambiguity equiv_class util.
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

  Implicit Type G : grammar Σ N.
  Implicit Type A : N.

  Definition sentence_iso G A w1 w2 : Prop :=
    (∀ t1, t1 ▷ A ={ G }=> w1 → ∃ t2, t2 ▷ A ={ G }=> w2 ∧ tree_iso t1 t2) ∧
    (∀ t2, t2 ▷ A ={ G }=> w2 → ∃ t1, t1 ▷ A ={ G }=> w1 ∧ tree_iso t1 t2).

  Global Instance sentence_equiv G A : Equiv (sentence Σ) := sentence_iso G A.

  (* sentence_iso is also an equivalent relation *)

  Global Instance sentence_iso_refl G A : Reflexive (sentence_iso G A).
  Proof.
    intros w. split => t Ht; exists t; naive_solver.
  Qed.

  Global Instance sentence_iso_sym G A : Symmetric (sentence_iso G A).
  Proof.
    intros w1 w2 [H1 H2]. split => t Ht.
    - destruct (H2 _ Ht) as [t' Ht']. exists t'. naive_solver.
    - destruct (H1 _ Ht) as [t' Ht']. exists t'. naive_solver.
  Qed.

  Global Instance sentence_iso_trans G A : Transitive (sentence_iso G A).
  Proof.
    intros w1 w2 w3 [H12 H21] [H23 H32]. split => t Ht.
    - destruct (H12 _ Ht) as [t1 [Ht1 ?]]. destruct (H23 _ Ht1) as [t2 [? ?]].
      exists t2. split; first naive_solver. etrans; eauto.
    - destruct (H32 _ Ht) as [t1 [Ht1 ?]]. destruct (H21 _ Ht1) as [t2 [? ?]].
      exists t2. split; first naive_solver. etrans; eauto.
  Qed.

  Global Instance sentence_iso_equiv G A : Equivalence (sentence_iso G A) := {
    Equivalence_Reflexive := sentence_iso_refl G A;
    Equivalence_Symmetric := sentence_iso_sym G A;
    Equivalence_Transitive := sentence_iso_trans G A;
  }.

  (* Synthesis conditions: G is the refined grammar we need to solve. *)

  Definition acceptance G A n (W : vec (sentence Σ) n) (T : vec (@tree Σ N) n) : Prop :=
    ∀ i, T !!! i ▷ A ={ G }=> W !!! i.

  Fixpoint reformat_tree_aux t w :=
    match t with
    | ε_tree A => (ε_tree A, w)
    | token_tree A tk =>
      match w with
      | [] => (token_tree A tk, [])
      | tk' :: w' => (token_tree A tk', w')
      end
    | unary_tree A t =>
      let (t', w') := reformat_tree_aux t w in
      (unary_tree A t', w')
    | binary_tree A t1 t2 =>
      let (t1', w1) := reformat_tree_aux t1 w in
      let (t2', w2) := reformat_tree_aux t2 w1 in
      (binary_tree A t1' t2', w2)
    end.

  Definition reformat_tree t w := (reformat_tree_aux t w).1.

  Local Lemma destruct_pair_lemma {α β : Type} (p : α * β) a b :
    p = (a, b) → p.1 = a ∧ p.2 = b.
  Proof. naive_solver. Qed.

  Local Ltac destruct_pair :=
    repeat match goal with
    | [ H : _ = (_, _) |- _ ] => apply destruct_pair_lemma in H as [? ?]
    end.

  Lemma reformat_tree_aux_consume t w :
    length (word t) ≤ length w →
    (reformat_tree_aux t w).2 = drop (length (word t)) w.
  Proof.
    generalize dependent w. unfold reformat_tree.
    induction t => w Hp /=; repeat case_match; destruct_pair; simplify_eq/=.
    all: try naive_solver.
    rewrite app_length in Hp.
    rewrite IHt1; first lia.
    rewrite IHt2; first by rewrite drop_length; lia.
    by rewrite app_length drop_drop.
  Qed.

  Lemma reformat_tree_iso t w :
    token <$> word t `prefix_of` token <$> w →
    (reformat_tree t w) ≡ t.
  Proof.
    generalize dependent w. unfold reformat_tree.
    induction t => w Hp /=; repeat case_match; destruct_pair; simplify_eq/=.
    - apply ε_tree_iso.
    - by apply token_tree_iso.
    - apply token_tree_iso. inversion Hp; naive_solver.
    - apply unary_tree_iso. naive_solver.
    - apply binary_tree_iso; rewrite fmap_app in Hp.
      + apply prefix_app_l in Hp. naive_solver.
      + apply prefix_app_drop in Hp as [Hpl Hpr].
        rewrite fmap_length -fmap_drop -reformat_tree_aux_consume in Hpr.
        { apply prefix_length in Hpl. by rewrite !fmap_length in Hpl. }
        naive_solver.
  Qed.

  Lemma reformat_tree_word_prefix t w :
    token <$> word t `prefix_of` token <$> w →
    word (reformat_tree t w) `prefix_of` w.
  Proof.
    generalize dependent w. unfold reformat_tree.
    induction t => w Hp /=; repeat case_match; destruct_pair; simplify_eq/=.
    - apply prefix_nil.
    - inversion Hp; naive_solver.
    - apply prefix_cons, prefix_nil.
    - naive_solver.
    - rewrite fmap_app in Hp. apply prefix_app_drop in Hp as [Hpl Hpr].
      apply prefix_app_drop. split; first naive_solver.
      rewrite fmap_length -fmap_drop in Hpr.
      have ? : length (word t1) ≤ length w.
      { apply prefix_length in Hpl. by rewrite !fmap_length in Hpl. }
      rewrite -reformat_tree_aux_consume in Hpr => //.
      erewrite trees_iso_word_length_eq; last by apply reformat_tree_iso.
      rewrite -reformat_tree_aux_consume => //.
      naive_solver.
  Qed.

  Lemma reformat_tree_word t w :
    token <$> word t = token <$> w →
    word (reformat_tree t w) = w.
  Proof.
    intros Heq. apply prefix_length_eq.
    - apply reformat_tree_word_prefix. rewrite Heq. apply prefix_refl.
    - have Heqf : length (token <$> word t) = length (token <$> w) by rewrite Heq.
      have <- : length (word t) = length w by rewrite !fmap_length in Heqf.
      suff : length (word t) = length (word (reformat_tree t w)) by lia.
      apply trees_iso_word_length_eq. symmetry. apply reformat_tree_iso.
      rewrite Heq. apply prefix_refl.
  Qed.

  Definition rejection G A n (W : vec (sentence Σ) n) (T : vec (@tree Σ N) n) : Prop :=
    ∀ i j, i ≠ j → ¬ (reformat_tree (T !!! j) (W !!! i) ▷ A ={ G }=> W !!! i).

  Definition synthesis_conditions G A n W T : Prop :=
    acceptance G A n W T ∧ rejection G A n W T.

  Definition valid n (W : vec (sentence Σ) n) : Prop :=
    ∀ i j, token <$> W !!! i = token <$> W !!! j.

  Lemma tree_not_iso_with_rejected G A n W T :
    valid n W →
    synthesis_conditions G A n W T →
    ∀ i t, t ▷ A ={ G }=> W !!! i → ∀ j, j ≠ i → t ≢ T !!! j.
  Proof.
    intros Hv [Hacc Hrej] i t Ht j ? Hyp.
    eapply Hrej with (i := i); eauto.
    have -> : reformat_tree (T !!! j) (W !!! i) = t.
    { eapply trees_iso_same_word_eq.
      - etrans. 2: symmetry; eauto.
        apply reformat_tree_iso.
        destruct (Hacc j) as [_ [-> _]].
        erewrite Hv; apply prefix_refl.
      - rewrite reformat_tree_word. 1: by destruct (Hacc j) as [_ [-> _]].
        by destruct Ht as [? [? ?]]. }
    done.
  Qed.

  Definition sentence_equiv_class G A := @equiv_class (sentence Σ) (sentence_iso G A).

  Theorem sentence_equiv_classes_disjoint G A n W T :
    valid n W →
    synthesis_conditions G A n W T →
    ∀ i j l k, i ≠ j →
      sentence_equiv_class G A (W !!! i) l →
      sentence_equiv_class G A (W !!! j) k →
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