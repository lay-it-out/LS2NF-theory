From stdpp Require Import relations.
From Coq Require Import ssreflect.

(* sentence *)

Definition position : Type := nat * nat.

Record token (Σ : Type) := {
  letter : Σ;
  pos : position;
}.

Notation "a @ p" := {|
  letter := a;
  pos := p;
|} (at level 40).

Definition sentence (Σ : Type) : Type := list (token Σ).

Definition unary_predicate (Σ : Type) : Type := sentence Σ → Prop.

Definition binary_predicate (Σ : Type) : Type := sentence Σ → sentence Σ → Prop.

(* grammar *)

Inductive clause (Σ N : Type) : Type :=
  | ε : clause Σ N
  | atom : Σ → clause Σ N
  | unary : N → unary_predicate Σ → clause Σ N
  | binary : N → N → binary_predicate Σ → clause Σ N
  .

Arguments ε {_} {_}.
Arguments atom {_} {_}.
Arguments unary {_} {_}.
Arguments binary {_} {_}.

Definition nonterm {Σ N : Type} (A : N) : clause Σ N := unary A (λ _, True).

Record grammar (Σ N : Type) := {
  start : N;
  P : N → list (clause Σ N);
}.

Arguments start {_} {_}.
Arguments P {_} {_}.

Notation "G ⊢ A ↦ α" := (α ∈ P G A) (at level 60).

(* parsing *)

Inductive tree (Σ N : Type) : Type :=
  | ε_tree : N → tree Σ N
  | token_tree : N → token Σ → tree Σ N
  | unary_tree : N → tree Σ N → tree Σ N
  | binary_tree : N → tree Σ N → tree Σ N → tree Σ N
  .

Arguments ε_tree {_} {_}.
Arguments token_tree {_} {_}.
Arguments unary_tree {_} {_}.
Arguments binary_tree {_} {_}.

Definition root {Σ N : Type} (t : tree Σ N) : N :=
  match t with
  | ε_tree R => R
  | token_tree R _ => R
  | unary_tree R _ => R
  | binary_tree R _ _ => R
  end.

Fixpoint sentence_of {Σ N : Type} (t : tree Σ N) : sentence Σ :=
  match t with
  | ε_tree _ => []
  | token_tree _ tk => [tk]
  | unary_tree _ t' => sentence_of t'
  | binary_tree _ t1 t2 => sentence_of t1 ++ sentence_of t2
  end.

Inductive valid {Σ N : Type} : grammar Σ N → tree Σ N → Prop :=
  | valid_ε_tree G R :
    G ⊢ R ↦ ε →
    valid G (ε_tree R)
  | valid_token_tree G R a p :
    G ⊢ R ↦ atom a →
    valid G (token_tree R (a @ p))
  | valid_unary_tree G R A φ t w :
    G ⊢ R ↦ unary A φ →
    root t = A →
    valid G t →
    sentence_of t = w →
    (w ≠ [] → φ w) →
    valid G (unary_tree R t)
  | valid_binary_tree G R A B φ t1 t2 w1 w2 :
    G ⊢ R ↦ binary A B φ →
    valid G t1 →
    valid G t2 →
    root t1 = A →
    root t2 = B →
    sentence_of t1 = w1 →
    sentence_of t2 = w2 →
    (w1 ≠ [] → w2 ≠ [] → φ w1 w2) →
    valid G (binary_tree R t1 t2)
  .

Notation "✓{ G } t" := (valid G t) (at level 70, format "'✓{' G '}'  t").

Definition witness {Σ N : Type} (t : tree Σ N) (G : grammar Σ N) (A : N) (w : sentence Σ) : Prop :=
  ✓{G} t ∧ root t = A ∧ sentence_of t = w.

Notation "t ▷ A ={ G }=> w" := (witness t G A w) (at level 40).

Lemma ε_tree_witness {Σ N : Type} (G : grammar Σ N) A :
  G ⊢ A ↦ ε → (ε_tree A) ▷ A ={G}=> [].
Proof.
  intros. repeat split.
  by constructor.
Qed.

Lemma token_tree_witness {Σ N : Type} (G : grammar Σ N) A a p :
  G ⊢ A ↦ atom a → (token_tree A (a @ p)) ▷ A ={G}=> [a @ p].
Proof.
  intros. repeat split.
  by constructor.
Qed.

Lemma unary_tree_witness {Σ N : Type} (G : grammar Σ N) A B φ w t :
  G ⊢ A ↦ unary B φ →
  t ▷ B ={G}=> w →
  (w ≠ [] → φ w) →
  (unary_tree A t) ▷ A ={G}=> w.
Proof.
  intros ? [? [? ?]]. repeat split.
  - econstructor; eauto.
  - by simpl.
Qed.

Lemma binary_tree_witness {Σ N : Type} (G : grammar Σ N) A B C φ w1 w2 t1 t2 :
  G ⊢ A ↦ binary B C φ →
  t1 ▷ B ={G}=> w1 →
  t2 ▷ C ={G}=> w2 →
  (w1 ≠ [] → w2 ≠ [] → φ w1 w2) →
  (binary_tree A t1 t2) ▷ A ={G}=> (w1 ++ w2).
Proof.
  intros ? [? [? ?]] [? [? ?]]. repeat split.
  - econstructor; eauto.
  - simpl. congruence.
Qed.

(* derivation *)

Definition derive {Σ N : Type} (G : grammar Σ N) (A : N) (w : sentence Σ) : Prop :=
  ∃ t, t ▷ A ={G}=> w.

Notation "G ⊨ A ⇒ w" := (derive G A w) (at level 65).

(* proof rules for the judgement G ⊨ A ⇒ w *)

Lemma derive_ε {Σ N : Type} (G : grammar Σ N) A :
  G ⊢ A ↦ ε → G ⊨ A ⇒ [].
Proof.
  intros. exists (ε_tree A). 
  split; last done.
  by constructor.
Qed.

Lemma derive_atom {Σ N : Type} (G : grammar Σ N) A a p :
  G ⊢ A ↦ atom a → G ⊨ A ⇒ [a @ p].
Proof.
  intros. exists (token_tree A (a @ p)).
  split; last done.
  by constructor.
Qed.

Lemma derive_unary {Σ N : Type} (G : grammar Σ N) A B (φ : unary_predicate Σ) w :
  G ⊢ A ↦ unary B φ →
  G ⊨ B ⇒ w →
  (w ≠ [] → φ w) →
  G ⊨ A ⇒ w.
Proof.
  intros ? [t [? [? ?]]] ?. exists (unary_tree A t).
  split; last done.
  econstructor; eauto.
Qed.

Lemma derive_binary {Σ N : Type} (G : grammar Σ N) A B C (φ : binary_predicate Σ) w1 w2 :
  G ⊢ A ↦ binary B C φ →
  G ⊨ B ⇒ w1 →
  G ⊨ C ⇒ w2 →
  (w1 ≠ [] → w2 ≠ [] → φ w1 w2) →
  G ⊨ A ⇒ w1 ++ w2.
Proof.
  intros ? [t1 [? [? Hw1]]] [t2 [? [? Hw2]]] ?.
  exists (binary_tree A t1 t2). repeat split.
  - econstructor; eauto.
  - simpl. by rewrite Hw1 Hw2.
Qed.

(* nullability *)

Definition nullable {Σ N : Type} (G : grammar Σ N) (A : N) : bool.
Admitted.

Lemma nullable_spec {Σ N : Type} (G : grammar Σ N) A :
  nullable G A = true → G ⊨ A ⇒ [].
Admitted.

Lemma binary_nullable_l {Σ N : Type} (G : grammar Σ N) A B φ E w :
  G ⊢ A ↦ binary E B φ →
  nullable G E = true →
  G ⊨ B ⇒ w →
  G ⊨ A ⇒ w.
Proof.
  intros ? Hn [t [? [? Hw]]].
  destruct (nullable_spec _ _ Hn) as [tε [? [? Hε]]].
  exists (binary_tree A tε t). repeat split.
  - by econstructor; eauto.
  - simpl. by rewrite Hw Hε app_nil_l.
Qed.

Lemma binary_nullable_r {Σ N : Type} (G : grammar Σ N) A B φ E w :
  G ⊢ A ↦ binary B E φ →
  nullable G E = true →
  G ⊨ B ⇒ w →
  G ⊨ A ⇒ w.
Proof.
  intros ? Hn [t [? [? Hw]]].
  destruct (nullable_spec _ _ Hn) as [tε [? [? Hε]]].
  exists (binary_tree A t tε). repeat split.
  - by econstructor; eauto.
  - simpl. by rewrite Hw Hε app_nil_r.
Qed.

(* Lemma nonterm_derive {Σ N : Type} (G : grammar Σ N) A w :
  G ⊨ A ⇒ w → G ⊨ nonterm A ⇒ w.
Proof.
  intros H.
  inversion H.
  by constructor.
Qed.

Lemma unary_derives_from_nonterm {Σ N : Type} (G : grammar Σ N) (A : N) w (φ : unary_predicate Σ) :
  G ⊨ A ⇒ w →
  φ w →
  G ⊨ unary A φ ⇒ w.
Proof.
  intros HA Hφ.
  inversion HA.
  by constructor.
Qed.

Lemma binary_null_l_derives_from_nonterm {Σ N : Type} (G : grammar Σ N) E A w (φ : binary_predicate Σ) :
  nullable G E = true →
  G ⊨ A ⇒ w →
  G ⊨ binary E A φ ⇒ w.
Proof.
  intros HE HA.
  rewrite <- app_nil_l.
  constructor; last done.
  all: try apply nullable_spec in HE.
  all: by apply nonterm_derive.
Qed.

Lemma binary_null_r_derives_from_nonterm {Σ N : Type} (G : grammar Σ N) E A w (φ : binary_predicate Σ) :
  nullable G E = true →
  G ⊨ A ⇒ w →
  G ⊨ binary A E φ ⇒ w.
Proof.
  intros HE HA.
  rewrite <- app_nil_r.
  constructor; last done.
  all: try apply nullable_spec in HE.
  all: by apply nonterm_derive.
Qed. *)

(* acyclic *)

Inductive derive_nonterm {Σ N : Type} : grammar Σ N → N → N → Prop :=
  | derive_nonterm_refl G A : derive_nonterm G A A
  | derive_nonterm_unary G A B φ :
    (* the derivation is not really A =>* B, but constraint omitted *)
    G ⊢ A ↦ unary B φ → derive_nonterm G A B
  | derive_nonterm_binary_nullable_l G A E B φ :
    G ⊢ A ↦ binary E B φ → nullable G E → derive_nonterm G A B
  | derive_nonterm_binary_nullable_r G A B E φ :
    G ⊢ A ↦ binary B E φ → nullable G E → derive_nonterm G A B
  .

Notation "A ⇒{ G } B" := (derive_nonterm G A B) (at level 65).

Class Acyclic {Σ N : Type} (G : grammar Σ N) := {
  N_lt : relation N;
  N_lt_wf : wf N_lt;
  acyclic : ∀ A B, A ⇒{G} B → N_lt B A;
}.
