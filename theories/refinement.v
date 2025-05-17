From stdpp Require Import relations.
From Coq Require Import ssreflect.
From LS2NF Require Import grammar witness ambiguity slice.

Section refinement.

  Context {Σ N : Type} `{!EqDecision Σ} `{!EqDecision N}.
  Implicit Type G : grammar Σ N.
  Open Scope grammar_scope.

  (* We _refine_ a clause by strengthening its layout predicate (if any).
     The strengthening clause [α'] is said a _refinement_ of the original [α],
     defined as [clause refine α' α]. *)
  Inductive clause_refine : relation (clause Σ N) :=
    | ε_refine : clause_refine ε ε
    | atom_refine a : clause_refine (atom a) (atom a)
    | unary_refine A φ' φ : 
      (∀ w, app₁ φ' w = true → app₁ φ w = true) →
      clause_refine (unary A φ') (unary A φ)
    | binary_refine Al Ar φ' φ :
      (∀ w1 w2, app₂ φ' w1 w2 = true → app₂ φ w1 w2 = true) →
      clause_refine (binary Al Ar φ') (binary Al Ar φ)
    .

  (* A grammar [G'] is said a _refinement_ of [G] if all clauses in [G'] are refinements
     (as defined by [clause_refine]) of those in [G]. *)
  Definition grammar_refine : relation (grammar Σ N) := λ G' G,
    ∀ A α', A ↦ α' ∈ G' → ∃ α, clause_refine α' α ∧ A ↦ α ∈ G.
  
  Lemma witness_refine G G' t A w :
    grammar_refine G' G →
    t ▷ A ={ G' }=> w →
    t ▷ A ={ G }=> w.
  Proof.
    intros Hr.
    move: A w. induction t as [?|??|?? IHt|?? IHt1 ? IHt2] => A w Ht.
    all: have [/=? [/=? Hv]] := Ht; subst.
    all: inversion Hv as [? Hp|??? Hp|??? Hp|???? Hp]; subst.
    all: destruct (Hr _ _ Hp) as [? [Hcr ?]]; inversion Hcr; subst.
    - by apply witness_ε.
    - by apply witness_atom.
    - eapply witness_unary; last split; eauto. by apply IHt.
    - eapply witness_binary; last split; last split; eauto; by [apply IHt1 | apply IHt2].
  Qed.

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

  Fixpoint fill (w : sentence Σ) (s : lf_tree) : option (@tree Σ N) :=
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
    | lf_unary_tree A s => t ← fill w s; Some (unary_tree A t)
    | lf_binary_tree A sl sr =>
      tl ← fill (take (lf_tree_size sl) w) sl;
      tr ← fill (drop (lf_tree_size sl) w) sr;
      Some (binary_tree A tl tr)
    end.
  
  Fixpoint erase (t : @tree Σ N) : lf_tree :=
    match t with
    | ε_tree A => lf_ε_tree A
    | token_tree A pt => lf_token_tree A (token pt)
    | unary_tree A t => lf_unary_tree A (erase t)
    | binary_tree A tl tr => lf_binary_tree A (erase tl) (erase tr)
    end.

  Lemma fill_Some_size w s t' :
    fill w s = Some t' → lf_tree_size s = length w.
  Proof.
    move: w t'. induction s as [|??|A s IHs|A sl IHsl sr IHsr] => w t' /=.
    - by case_match.
    - by repeat case_match.
    - rewrite bind_Some. intros [t [? ?]].
      erewrite IHs; eauto.
    - rewrite bind_Some. intros [t1 [? H]].
      rewrite bind_Some in H. destruct H as [t2 [? ?]].
      erewrite IHsl; eauto. erewrite IHsr; eauto.
      rewrite -length_app. apply f_equal. apply take_drop.
  Qed.

  Lemma fill_erase w t t' :
    fill w (erase t) = Some t' → fill (word t) (erase t') = Some t.
  Proof.
      move: w t'. induction t as [|A pt|A t IHt|A tl IHtl tr IHtr] => /= w t'.
      - case_match => // Ht'. apply Some_inj in Ht'. by subst.
      - case_match => //. case_match => //. case_bool_decide => // Ht'.
        apply Some_inj in Ht'. subst => /=. case_bool_decide; congruence.
      - rewrite bind_Some. intros [t1 [Ht1 Ht']]. apply IHt in Ht1.
        apply Some_inj in Ht'. by rewrite -Ht' /= Ht1.
      - rewrite bind_Some. intros [t1 [Ht1 Ht']]. apply IHtl in Ht1.
        apply bind_Some in Ht' as [t2 [Ht2 Ht']]. apply IHtr in Ht2.
        apply Some_inj in Ht'. rewrite -Ht' /=.
        erewrite fill_Some_size; eauto. rewrite take_app_length Ht1 /=.
        by rewrite drop_app_length Ht2.
  Qed.

  (* Sentence [w'] is a _reformat_ of [w] if [w'] does not introduce any more parse trees. *)
  Definition reformat G A : relation (sentence Σ) := λ w' w,
    ∀ t, t ▷ A ={ G }=> w' →
      ∃ t', fill w (erase t) = Some t' ∧ t' ▷ A ={ G }=> w.

  Theorem dis_ambiguity G G' A w w' tₐ :
    reformat G A w' w →
    grammar_refine G' G →
    (∀ t, t ▷ A ={ G }=> w → t ≠ tₐ → 
      ∃ t', fill w' (erase t) = Some t' ∧ ¬ (t' ▷ A ={ G' }=> w')) →
    ∀ t', t' ▷ A ={ G' }=> w' → fill w' (erase tₐ) = Some t'.
  Proof.
    intros Hr ? Hc t' Ht'.
    have Htt' := Ht'. eapply witness_refine in Htt'; eauto.
    apply Hr in Htt' as [t [Htt' Ht]].
    destruct (bool_decide (t = tₐ)) eqn:Heq.
    - rewrite bool_decide_eq_true in Heq. subst.
      destruct Ht' as [_ [? _]]. subst. eapply fill_erase. eauto.
    - rewrite bool_decide_eq_false in Heq.
      apply Hc in Ht as [t'' [? Ht'']] => //.
      apply fill_erase in Htt'. have [_ [? _]] := Ht'. subst.
      congruence.
  Qed.
    
  Corollary dis_ambiguity' G G' A w w' tₐ :
    reformat G A w' w →
    grammar_refine G' G →
    (∀ t, t ▷ A ={ G }=> w → t ≠ tₐ → 
      ∃ t', fill w' (erase t) = Some t' ∧ ¬ (t' ▷ A ={ G' }=> w')) →
    ¬ (derive_amb G' A w').
  Proof.
    intros ??? [t1 [t2 [Ht1 [Ht2 ?]]]].
    eapply dis_ambiguity in Ht1; eauto.
    eapply dis_ambiguity in Ht2; eauto.
    congruence.
  Qed.

End refinement.