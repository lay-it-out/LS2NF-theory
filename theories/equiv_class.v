From stdpp Require Import relations.
From Coq Require Import ssreflect.

Section equiv_class.
  Context {A : Type} {R : relation A} `{!Equivalence R}.

  Global Instance Equivalence_equiv : Equiv A := R.

  Definition equiv_class (a : A) (l : list A) : Prop := Forall (λ x, x ≡ a) l.

  Lemma equiv_class_disjoint a l b k :
    equiv_class a l →
    equiv_class b k →
    a ≢ b →
    l ## k.
  Proof.
    rewrite /equiv_class !Forall_forall.
    intros Ha Hb Hne x Hxl Hxk.
    apply Ha in Hxl. apply Hb in Hxk. apply Hne.
    by trans x.
  Qed.

End equiv_class.