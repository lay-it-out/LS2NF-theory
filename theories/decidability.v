From stdpp Require Import relations.
From Coq Require Import ssreflect.
From Coq.Program Require Import Wf.
From ambig Require Import util grammar acyclic sub_derive.

Section decidability.

  Variable Σ N : Type.
  Context `{EqDecision Σ}.
  Context `{EqDecision N}.

  Variable G : grammar Σ N.
  Context `{acyclic G}.

  (* Implicit Type A Al Ar B Bl Br : N. *)
  Implicit Type w h : sentence Σ.

  Definition sig_lt : relation (sentence Σ * N) :=
    or_relation (ltof (sentence Σ) length) (flip (succ G)).

  Lemma sig_lt_wf :
    wf sig_lt.
  Proof.
    intros. apply or_relation_wf.
    - apply well_founded_ltof.
    - by apply acyclic_succ_flip_wf.
  Qed.

  Definition nonempty_partition w : list (sentence Σ * sentence Σ) :=
    match w with
    | [] => []
    | _ :: w' => (λ k, (take k w, drop k w)) <$> (nat_range (length w'))
    end.

  Lemma nonempty_partition_decrease w wl wr :
    (wl, wr) ∈ nonempty_partition w →
    length wl < length w ∧ length wr < length w.
  Proof.
    destruct w.
    - inversion 1.
    - intros Hin. apply elem_of_list_fmap in Hin as [x [Hp Hx]].
      inversion Hp; subst; clear Hp.
      apply nat_range_elem_of in Hx.
      rewrite take_length drop_length cons_length. lia.
  Qed.

  Lemma nonempty_partition_spec w wl wr :
    (wl, wr) ∈ nonempty_partition w ↔
    w = wl ++ wr ∧ wl ≠ [] ∧ wr ≠ [].
  Admitted.

  Program Fixpoint check_derive A w {measure (w, A) sig_lt} : bool :=
    big_or (clauses G A) (λ p, match p with existT α Hα =>
      match α with
      | ε => bool_decide (w = [])
      | atom a =>
        match w with
        | [tk] => bool_decide (letter tk = a)
        | _ => false
        end
      | unary B φ => apply₁ φ w && check_derive B w
      | binary Bl Br φ =>
        when (G ⊨ Bl ⇒ []) (λ _, check_derive Br w) ||
        when (G ⊨ Br ⇒ []) (λ _, check_derive Bl w) ||
        big_or (nonempty_partition w)
          (λ wp, match wp with existT (wl, wr) Hwp =>
            apply₂ φ wl wr && check_derive Bl wl && check_derive Br wr
          end)
      end
    end).
  Next Obligation.
    intros. naive_solver.
  Qed.
  Next Obligation.
    intros. naive_solver.
  Qed.
  Next Obligation.
    intros. subst. right; split => //.
    eapply succ_unary; eauto.
  Qed.
  Next Obligation.
    intros. subst. right; split => //.
    eapply succ_right; eauto.
  Qed.
  Next Obligation.
    intros. subst. right; split => //.
    eapply succ_left; eauto.
  Qed.
  Next Obligation.
    intros. subst. left.
    simpl in *.
    edestruct nonempty_partition_decrease; eauto.
  Qed.
  Next Obligation.
    intros. subst. left.
    simpl in *.
    edestruct nonempty_partition_decrease; eauto.
  Qed.
  Next Obligation.
    by apply measure_wf, sig_lt_wf.
  Qed.

  (* equation lemma *)
  Lemma check_derive_equation A w :
    check_derive A w =
    big_or (clauses G A) (λ p, match p with existT α Hα =>
      match α with
      | ε => bool_decide (w = [])
      | atom a =>
        match w with
        | [tk] => bool_decide (letter tk = a)
        | _ => false
        end
      | unary B φ => apply₁ φ w && check_derive B w
      | binary Bl Br φ =>
        when (G ⊨ Bl ⇒ []) (λ _, check_derive Br w) ||
        when (G ⊨ Br ⇒ []) (λ _, check_derive Bl w) ||
        big_or (nonempty_partition w)
          (λ wp, match wp with existT (wl, wr) Hwp =>
            apply₂ φ wl wr && check_derive Bl wl && check_derive Br wr
          end)
      end
    end).
  Admitted.

  Lemma check_derive_spec A w :
    check_derive A w = true ↔ G ⊨ A ⇒ w.
  Proof.
    split; intros H.
    - (* -> *)
      generalize dependent A.
      induction w as [w IHw] using (well_founded_induction (well_founded_ltof (sentence Σ) length)).
      induction A as [A IHA] using (well_founded_induction (acyclic_succ_flip_wf _ _ _ acyclic0)).
      rewrite check_derive_equation big_or_true.
      intros [[α Hp] Hα]. case_match; subst.
      + apply bool_decide_eq_true in Hα. subst.
        by apply derive_ε.
      + repeat case_match => //.
        apply bool_decide_eq_true in Hα. subst.
        destruct t. by apply derive_atom.
      + apply andb_true_iff in Hα as [? ?].
        eapply derive_unary; eauto.
        clear IHw. apply IHA; eauto.
        eapply succ_unary; eauto.
      + apply orb_true_iff in Hα as [Hα|Hα].
        apply orb_true_iff in Hα as [Hα|Hα].
        * apply when_true in Hα as [Hn ?]. destruct b.
          rewrite <-app_nil_l. eapply derive_binary; eauto.
          clear IHw. apply IHA; eauto.
          eapply succ_right; eauto.
        * apply when_true in Hα as [Hn ?]. destruct b.
          rewrite <-app_nil_r. eapply derive_binary; eauto.
          clear IHw. apply IHA; eauto.
          eapply succ_left; eauto.
        * apply big_or_true in Hα as [[[wl wr] Hpar] Hα].
          apply andb_true_iff in Hα as [Hα ?].
          apply andb_true_iff in Hα as [? ?].
          edestruct nonempty_partition_decrease; eauto.
          edestruct nonempty_partition_spec as [[Hw _] _]; eauto.
          rewrite Hw. eapply derive_binary; eauto.
    - (* <- *)
      destruct H as [t [? [? Ht]]].
      generalize dependent A.
      generalize dependent w.
      induction t; intros.
      all: inversion Ht; subst; clear Ht.
      all: rewrite check_derive_equation.
      all: apply big_or_true.
      + exists (existT ε H2).
        apply bool_decide_eq_true. done. 
      + exists (existT (atom a) H2).
        repeat case_match => //.
        apply bool_decide_eq_true. naive_solver.
      + exists (existT (unary (root t) φ) H3).
        apply andb_true_iff. naive_solver.
      + exists (existT (binary (root t1) (root t2) φ) H4).
        destruct (decide (word t1 = []));
          last destruct (decide (word t2 = [])).
        * have Hn : G ⊨ root t1 ⇒ [].
          { exists t1. by repeat split. }
          apply orb_true_iff. left.
          apply orb_true_iff. left.
          apply when_true. exists Hn.
          simpl in *. rewrite e app_nil_l. naive_solver.
        * have Hn : G ⊨ root t2 ⇒ [].
          { exists t2. by repeat split. }
          apply orb_true_iff. left.
          apply orb_true_iff. right.
          apply when_true. exists Hn.
          simpl in *. rewrite e app_nil_r. naive_solver.
        * apply orb_true_iff. right.
          apply big_or_true. simpl in *.
          have Hw : (word t1, word t2) ∈ nonempty_partition (word t1 ++ word t2).
          { apply nonempty_partition_spec. naive_solver. }
          exists (existT (word t1, word t2) Hw).
          apply andb_true_iff. split.
          apply andb_true_iff. split.
          all: naive_solver.
  Qed.

  Global Instance acyclic_derive_dec A w :
    Decision (G ⊨ A ⇒ w).
  Proof.
    destruct (check_derive A w) eqn:Heqn.
    - left. eapply check_derive_spec; eauto.
    - right. apply not_true_iff_false in Heqn. intros ?.
      by apply Heqn, check_derive_spec.
  Qed.

  (* reachable *)

  Definition partition w : list (sentence Σ * sentence Σ) :=
    match w with
    | [] => [([], [])]
    | _ :: w' => ([], w) :: ((λ k, (take k w, drop k w)) <$> (nat_range (length w)))
    end.

  Lemma partition_non_increase w wl wr :
    (wl, wr) ∈ partition w →
    length wl ≤ length w ∧ length wr ≤ length w.
  Proof.
  Admitted.

  Lemma partition_spec w wl wr :
    (wl, wr) ∈ partition w ↔ w = wl ++ wr.
  Admitted.

  Program Fixpoint check_reach (σ τ : N * sentence Σ) {measure (snd σ, fst σ) sig_lt} : bool :=
    match σ, τ with (A, w), (H, h) =>
      bool_decide (σ = τ) ||
        big_or (clauses G A) (λ p, match p with existT α Hα =>
          match α with
          | unary B φ => apply₁ φ w && check_reach (B, w) (H, h)
          | binary Bl Br φ =>
            big_or (partition w)
              (λ wp, match wp with existT (wl, wr) Hwp =>
                apply₂ φ wl wr && (
                  when (G ⊨ Br ⇒ wr) (λ _, check_reach (Bl, wl) (H, h)) ||
                  when (G ⊨ Bl ⇒ wl) (λ _, check_reach (Br, wr) (H, h))
                )
              end)
          | _ => false
          end
        end)
    end.
  Next Obligation.
    intros. subst.
    right. split => //.
    eapply succ_unary; eauto.
  Qed.
  Next Obligation.
    intros. subst. simpl in *.
    have ? : w = wl ++ wr by apply partition_spec.
    destruct wr; subst.
    - right. split. by rewrite app_nil_r.
      eapply succ_left; eauto.
    - left. rewrite /ltof app_length cons_length /=. lia.
  Qed.
  Next Obligation.
    intros. subst. simpl in *.
    have ? : w = wl ++ wr by apply partition_spec.
    destruct wl; subst.
    - right. split. by rewrite app_nil_l.
      eapply succ_right; eauto.
    - left. rewrite /ltof app_length cons_length /=. lia.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    by apply measure_wf, sig_lt_wf.
  Qed.

  Lemma check_reach_equation σ τ :
    check_reach σ τ =
    match σ, τ with (A, w), (H, h) =>
      bool_decide (σ = τ) ||
        big_or (clauses G A) (λ p, match p with existT α Hα =>
          match α with
          | unary B φ => apply₁ φ w && check_reach (B, w) (H, h)
          | binary Bl Br φ =>
            big_or (partition w)
              (λ wp, match wp with existT (wl, wr) Hwp =>
                apply₂ φ wl wr && (
                  when (G ⊨ Br ⇒ wr) (λ _, check_reach (Bl, wl) (H, h)) ||
                  when (G ⊨ Bl ⇒ wl) (λ _, check_reach (Br, wr) (H, h))
                )
              end)
          | _ => false
          end
        end)
    end.
  Admitted.

  Lemma check_reach_spec A w H h :
    check_reach (A, w) (H, h) = true ↔ reachable G (A, w) (H, h).
  Proof.
    rewrite -reachable_to_spec.
    split; intros He.
    - (* -> *)
      generalize dependent A.
      induction w as [w IHw] using (well_founded_induction (well_founded_ltof (sentence Σ) length)).
      unfold ltof in IHw.
      induction A as [A IHA] using (well_founded_induction (acyclic_succ_flip_wf _ _ _ acyclic0)).
      rewrite check_reach_equation orb_true_iff bool_decide_eq_true big_or_true.
      intros [->|Hα]. constructor.
      destruct Hα as [[α Hp] Hα]. case_match; subst; try done.
      + apply andb_true_iff in Hα as [? ?].
        eapply reachable_to_unary; eauto.
        clear IHw. apply IHA; eauto.
        eapply succ_unary; eauto.
      + apply big_or_true in Hα as [[[wl wr] Hpar] Hα].
        apply andb_true_iff in Hα as [? Hα].
        apply orb_true_iff in Hα as [Hα|Hα].
        all: apply when_true in Hα as [? ?].
        all: apply partition_spec in Hpar.
        all: rewrite Hpar.
        * eapply reachable_to_left; eauto. destruct wr.
          ** have Hwl : wl = w by symmetry; rewrite <-app_nil_r.
             rewrite Hwl. rewrite Hwl in H1.
             clear IHw. eapply IHA => //. eapply succ_left; eauto.
          ** clear IHA. eapply IHw => //.
             rewrite Hpar app_length cons_length. lia.
        * eapply reachable_to_right; eauto. destruct wl.
          ** have Hwr : wr = w by symmetry; rewrite <-app_nil_l.
             rewrite Hwr. rewrite Hwr in H1.
             clear IHw. eapply IHA => //. eapply succ_right; eauto.
          ** clear IHA. eapply IHw => //.
             rewrite Hpar app_length cons_length. lia.
    - (* <- *)
      generalize dependent A.
      generalize dependent w.
      induction 1; subst; intros.
      all: rewrite check_reach_equation orb_true_iff.
      1: left. 2-4: right; apply big_or_true.
      + by rewrite bool_decide_eq_true.
      + exists (existT (unary B φ) H0).
        apply andb_true_iff. naive_solver.
      + exists (existT (binary Bl Br φ) H0).
        apply big_or_true.
        have Hw : (w1, w2) ∈ partition (w1 ++ w2) by apply partition_spec; naive_solver.
        exists (existT (w1, w2) Hw).
        apply andb_true_iff. split => //.
        apply orb_true_iff. left. apply when_true. naive_solver.
      + exists (existT (binary Bl Br φ) H0).
        apply big_or_true.
        have Hw : (w1, w2) ∈ partition (w1 ++ w2) by apply partition_spec; naive_solver.
        exists (existT (w1, w2) Hw).
        apply andb_true_iff. split => //.
        apply orb_true_iff. right. apply when_true. naive_solver.
  Qed.

  Global Instance acyclic_reachable_dec A w H h :
    Decision (reachable G (A, w) (H, h)).
  Proof.
    destruct (check_reach (A, w) (H, h)) eqn:Heqn.
    - left. eapply check_reach_spec; eauto.
    - right. apply not_true_iff_false in Heqn. intros ?.
      by apply Heqn, check_reach_spec.
  Qed.

End decidability.

Arguments nonempty_partition {_}.
Arguments partition {_}.
Arguments check_derive {_} {_} {_} {_} _ {_}.
Arguments check_reach {_} {_} {_} {_} _ {_}.
