From stdpp Require Import relations.
From Coq Require Import ssreflect.
From LS2NF Require Import grammar ambiguity.

Section refinement.

  Context {Σ N : Type} `{!EqDecision Σ} `{!EqDecision N}.
  Implicit Type G : grammar Σ N.
  Open Scope grammar_scope.

  Inductive lf_tree : Type :=
    | lf_ε_tree (r : N)                             (* empty tree *)
    | lf_token_tree (r : N) (a : Σ)                 (* leaf tree *)
    | lf_unary_tree (r : N) (s : lf_tree)           (* unary tree *)
    | lf_binary_tree (r : N) (sl sr : lf_tree)      (* binary tree *)
    .

  Fixpoint lf_tree_size (s : lf_tree) : nat :=
    match s with
    | lf_ε_tree _ => 0
    | lf_token_tree _ _ => 1
    | lf_unary_tree _ s => lf_tree_size s
    | lf_binary_tree _ sl sr => lf_tree_size sl + lf_tree_size sr
    end.

  Fixpoint fill_positions (w : sentence Σ) (s : lf_tree) : option (@tree Σ N) :=
    match s with
    | lf_ε_tree A =>
      match w with
      | [] => Some (ε_tree A)
      | _ => None
      end
    | lf_token_tree A a => 
      match w with
      | [pt] => if bool_decide (token pt = a) then Some (token_tree A pt) else None
      | _ => None
      end
    | lf_unary_tree A s =>
      t ← fill_positions w s; Some (unary_tree A t)
    | lf_binary_tree A sl sr =>
      tl ← fill_positions (take (lf_tree_size sl) w) sl;
      tr ← fill_positions (drop (lf_tree_size sl) w) sr;
      Some (binary_tree A tl tr)
    end.

  Fixpoint erase_positions (t : @tree Σ N) : lf_tree :=
    match t with
    | ε_tree A => lf_ε_tree A
    | token_tree A (a @ _) => lf_token_tree A a
    | unary_tree A t => lf_unary_tree A (erase_positions t)
    | binary_tree A tl tr => lf_binary_tree A (erase_positions tl) (erase_positions tr)
    end.

  Lemma lf_tree_size_spec t :
    lf_tree_size (erase_positions t) = length (word t).
  Proof.
    induction t => //=.
    - by case_match.
    - rewrite length_app. congruence.
  Qed.

  Lemma fill_erase_positions t :
    fill_positions (word t) (erase_positions t) = Some t.
  Proof.
    induction t => //=.
    - case_match => /=. by case_bool_decide.
    - rewrite bind_Some. by exists t.
    - rewrite lf_tree_size_spec bind_Some. exists t1. split.
      + by rewrite take_app_length.
      + rewrite bind_Some. exists t2. by rewrite drop_app_length.
  Qed. 

  Definition lf_tree_witness G (s : lf_tree) (A : N) (w : sentence Σ) :=
    ∃ t, fill_positions w s = Some t ∧ t ▷ A ={ G }=> w.

  Definition grammar_refine : relation (grammar Σ N) := λ G' G,
    ∀ s A w, lf_tree_witness G' s A w → lf_tree_witness G s A w.

  Instance grammar_refine_refl : Reflexive grammar_refine.
  Proof. by intros ?. Qed.

  Instance grammar_refine_trans : Transitive grammar_refine.
  Proof. intros ?????????. naive_solver. Qed.

  Definition lf_trees G (A : N) (w : sentence Σ) (trees : list lf_tree) : Prop :=
    ∀ s, lf_tree_witness G s A w ↔ s ∈ trees.

  Lemma lf_trees_singleton_not_amb G A w :
    (∃ s, lf_trees G A w [s]) → ¬ (derive_amb G A w).
  Proof.
    intros [s Hs] [t1 [t2 [Ht1 [Ht2 ?]]]].
    have [_ [? _]] := Ht1.
    have [_ [? _]] := Ht2.
    have ? := fill_erase_positions t1.
    have ? := fill_erase_positions t2.
    have Hs1 : lf_tree_witness G (erase_positions t1) A w.
    { exists t1. split; [congruence|done]. }
    apply Hs, elem_of_list_singleton in Hs1.
    have Hs2 : lf_tree_witness G (erase_positions t2) A w.
    { exists t2. split; [congruence|done]. }
    apply Hs, elem_of_list_singleton in Hs2.
    congruence.
  Qed.

  Definition reformatted_words G (A : N) (w : sentence Σ)
      (trees : list lf_tree) (words : list (sentence Σ)) : Prop :=
    lf_trees G A w trees ∧ length words = length trees ∧ ∀ w', w' ∈ words →
      ∀ s, lf_tree_witness G s A w' → s ∈ trees.

  Theorem resolve_amb G A w trees words G' :
    reformatted_words G A w trees words →
    grammar_refine G' G →
    (∀ i si wi, trees !! i = Some si → words !! i = Some wi →
      lf_tree_witness G' si A wi) →
    (∀ i si j wj, i ≠ j → trees !! i = Some si → words !! j = Some wj →
      ¬ lf_tree_witness G' si A wj) →
    ∀ i wi, words !! i = Some wi → ¬ (derive_amb G' A wi).
  Proof.
    intros [? [? Hf]] Href Hacc Hrej i wi Hwi.
    apply lf_trees_singleton_not_amb.
    have [si ?] : is_Some (trees !! i).
    { apply lookup_lt_is_Some.
      have Hi : is_Some (words !! i) by naive_solver.
      apply lookup_lt_is_Some in Hi. lia. }
    exists si. split.
    - (* -> *)
      intros Hs. rewrite elem_of_list_singleton.
      have Hs' := Hs. apply Href, Hf in Hs'.
      2: { apply elem_of_list_lookup; eauto. }
      apply elem_of_list_lookup in Hs' as [k Hk].
      have [?|?] : (k = i) ∨ (k ≠ i) by lia. 1: congruence.
      eapply Hrej in Hk; eauto. congruence.
    - (* <- *)
      rewrite elem_of_list_singleton => ->.
      eapply Hacc; eauto.
  Qed.

End refinement.