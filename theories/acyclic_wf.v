From stdpp Require Import relations finite.
From Coq Require Import ssreflect.

Section acyclic_wf.
  Context {A : Type} (R : relation A).

  Lemma tc_refl_ex_loop x :
    tc R x x → ex_loop R x.
  Proof.
    intros. apply ex_loop_tc. cofix IH. econstructor; eauto.
  Qed.

  Lemma tc_flip x y :
    tc (flip R) x y → tc R y x.
  Proof.
    induction 1.
    - by apply tc_once.
    - eapply tc_r; eauto. 
  Qed.

  Definition acyclic (R : relation A) : Prop := ∀ x, ¬ ex_loop R x.

  Context `{!EqDecision A} `{!Finite A}.

  Lemma finite_acyclic_flip_wf :
    acyclic R → wf (flip R).
  Proof.
    intros Hno x. apply tc_finite_sn.
    - intros y ?. eapply Hno. apply tc_refl_ex_loop; eauto.
    - eexists => ? ?. apply elem_of_enum.
  Qed.

  Lemma finite_acyclic_wf :
    acyclic R → wf R.
  Proof.
    intros Hno x. apply tc_finite_sn.
    - intros y ?. eapply Hno. apply tc_refl_ex_loop, tc_flip; eauto.
    - eexists => ? ?. apply elem_of_enum.
  Qed.

End acyclic_wf.