From stdpp Require Import relations finite fin.
From Coq Require Import ssreflect.
From Coq Require Import Recdef.
From Coq.Program Require Import Wf.
From ambig Require Import util grammar acyclic.

Section decidability.

  Variable Σ N : Type.
  Context `{EqDecision Σ}.
  Context `{EqDecision N}.

  Global Instance token_eq_dec : EqDecision (token Σ).
  Proof.
    intros [a1 p1] [a2 p2].
    destruct (decide (a1 = a2 ∧ p1 = p2)); [left | right]; naive_solver.
  Qed.

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
      + exists (existT (unary (tree_root t) φ) H3).
        apply andb_true_iff. naive_solver.
      + exists (existT (binary (tree_root t1) (tree_root t2) φ) H4).
        destruct (decide (tree_word t1 = []));
          last destruct (decide (tree_word t2 = [])).
        * have Hn : G ⊨ tree_root t1 ⇒ [].
          { exists t1. by repeat split. }
          apply orb_true_iff. left.
          apply orb_true_iff. left.
          apply when_true. exists Hn.
          simpl in *. rewrite e app_nil_l. naive_solver.
        * have Hn : G ⊨ tree_root t2 ⇒ [].
          { exists t2. by repeat split. }
          apply orb_true_iff. left.
          apply orb_true_iff. right.
          apply when_true. exists Hn.
          simpl in *. rewrite e app_nil_r. naive_solver.
        * apply orb_true_iff. right.
          apply big_or_true. simpl in *.
          have Hw : (tree_word t1, tree_word t2) ∈ nonempty_partition (tree_word t1 ++ tree_word t2).
          { apply nonempty_partition_spec. naive_solver. }
          exists (existT (tree_word t1, tree_word t2) Hw).
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

  Program Fixpoint check_reach A w H h {measure (w, A) sig_lt} : bool :=
    bool_decide (A = H ∧ w = h) ||
    big_or (clauses G A) (λ p, match p with existT α Hα =>
      match α with
      | unary B φ => apply₁ φ w && check_reach B w H h
      | binary Bl Br φ =>
        when (G ⊨ Bl ⇒ []) (λ _, check_reach Br w H h) ||
        (* TODO: h = [] ? *)
        when (G ⊨ Br ⇒ []) (λ _, check_reach Bl w H h) ||
        big_or (nonempty_partition w)
          (λ wp, match wp with existT (wl, wr) Hwp =>
            apply₂ φ wl wr &&
            ((check_reach Bl wl H h && bool_decide (G ⊨ Br ⇒ wr))) ||
            ((bool_decide (G ⊨ Bl ⇒ wl) && check_reach Br wr H h))
          end)
      | _ => false
      end
    end).
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
    naive_solver.
  Qed.
  Next Obligation.
    naive_solver.
  Qed.
  Next Obligation.
    by apply measure_wf, sig_lt_wf.
  Qed.

  Lemma check_reach_equation A w H h :
    check_reach A w H h =
    bool_decide (A = H ∧ w = h) ||
    big_or (clauses G A) (λ p, match p with existT α Hα =>
      match α with
      | unary B φ => apply₁ φ w && check_reach B w H h
      | binary Bl Br φ =>
        when (G ⊨ Bl ⇒ []) (λ _, check_reach Br w H h) ||
        when (G ⊨ Br ⇒ []) (λ _, check_reach Bl w H h) ||
        big_or (nonempty_partition w)
          (λ wp, match wp with existT (wl, wr) Hwp =>
            apply₂ φ wl wr &&
            ((check_reach Bl wl H h && bool_decide (G ⊨ Br ⇒ wr)) ||
             (bool_decide (G ⊨ Bl ⇒ wl) && check_reach Br wr H h))
          end)
      | _ => false
      end
    end).
  Admitted.

  Lemma reachable_sub_sentence A w H h :
    reachable G A w H h → h `sublist_of` w.
  Admitted.

  Lemma check_reach_spec A w H h :
    h ≠ [] →
    check_reach A w H h = true ↔ reachable G A w H h.
  Proof.
    intros Hh.
    split; intros He.
    - (* -> *)
      generalize dependent A.
      induction w as [w IHw] using (well_founded_induction (well_founded_ltof (sentence Σ) length)).
      induction A as [A IHA] using (well_founded_induction (acyclic_succ_flip_wf _ _ _ acyclic0)).
      rewrite check_reach_equation orb_true_iff bool_decide_eq_true big_or_true.
      intros [[? ?]|Hα]. by constructor.
      destruct Hα as [[α Hp] Hα]. case_match; subst; try done.
      + apply andb_true_iff in Hα as [? ?].
        eapply reachable_unary; eauto.
        clear IHw. apply IHA; eauto.
        eapply succ_unary; eauto.
      + apply orb_true_iff in Hα as [Hα|Hα].
        apply orb_true_iff in Hα as [Hα|Hα].
        * apply when_true in Hα as [Hn ?]. destruct b.
          have -> : w = [] ++ w by rewrite app_nil_l.
          eapply reachable_right; eauto.
          clear IHw. apply IHA; eauto.
          eapply succ_right; eauto.
        * apply when_true in Hα as [Hn ?]. destruct b.
          have -> : w = w ++ [] by rewrite app_nil_r.
          eapply reachable_left; eauto.
          clear IHw. apply IHA; eauto.
          eapply succ_left; eauto.
        * apply big_or_true in Hα as [[[wl wr] Hpar] Hα].
          apply andb_true_iff in Hα as [? Hα].
          apply orb_true_iff in Hα as [Hα|Hα].
          all: apply andb_true_iff in Hα as [? ?].
          all: edestruct nonempty_partition_decrease; eauto.
          all: edestruct nonempty_partition_spec as [[Hw _] _]; eauto.
          all: rewrite Hw.
          ** eapply reachable_left; eauto. by eapply bool_decide_eq_true.
          ** eapply reachable_right; eauto. by eapply bool_decide_eq_true.
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
        have ? : w1 ≠ [].
        { intros ->.
          apply reachable_sub_sentence, sublist_nil_r in He.
          contradiction. }
        destruct (decide (w2 = [])).
        * apply orb_true_iff. left.
          apply orb_true_iff. right.
          have Hn : G ⊨ Br ⇒ [] by congruence.
          apply when_true. exists Hn.
          rewrite e app_nil_r. naive_solver.
        * apply orb_true_iff. right.
          apply big_or_true. simpl in *.
          have Hw : (w1, w2) ∈ nonempty_partition (w1 ++ w2).
          { apply nonempty_partition_spec. naive_solver. }
          exists (existT (w1, w2) Hw).
          apply andb_true_iff. split => //.
          apply orb_true_iff. left. apply andb_true_iff.
          split; [naive_solver | by apply bool_decide_eq_true].
      + exists (existT (binary Bl Br φ) H0).
        have ? : w2 ≠ [].
        { intros ->.
          apply reachable_sub_sentence, sublist_nil_r in He.
          contradiction. }
        destruct (decide (w1 = [])).
        * apply orb_true_iff. left.
          apply orb_true_iff. left.
          have Hn : G ⊨ Bl ⇒ [] by congruence.
          apply when_true. exists Hn.
          rewrite e app_nil_l. naive_solver.
        * apply orb_true_iff. right.
          apply big_or_true. simpl in *.
          have Hw : (w1, w2) ∈ nonempty_partition (w1 ++ w2).
          { apply nonempty_partition_spec. naive_solver. }
          exists (existT (w1, w2) Hw).
          apply andb_true_iff. split => //.
          apply orb_true_iff. right. apply andb_true_iff.
          split; [by apply bool_decide_eq_true | naive_solver].
  Qed.

End decidability.