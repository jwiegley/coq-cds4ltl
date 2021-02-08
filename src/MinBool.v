Set Warnings "-local-declaration".

Require Import
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid.

(***********************************************************************
 * This is a minimal Boolean Logic comprised of ∨, ¬ and three axioms. *)

Module Type MinimalBooleanLogic.

Parameter t : Type.             (* The type of boolean propositions *)

Parameter not : t -> t.
Parameter or : t -> t -> t.
Parameter true : t.
Parameter false : t.
Parameter impl : t -> t -> Prop.

Definition eqv (x y : t) : Prop := impl x y /\ impl y x.

Notation "¬ p"   := (not p)    (at level 0, right associativity).
Infix    "∨"     := or         (at level 46, right associativity).
Notation "p → q" := (¬ p ∨ q)  (at level 51, right associativity).
Notation "⊤"     := true       (at level 0, no associativity).
Notation "⊥"     := false      (at level 0, no associativity).
Infix    "⟹"    := impl       (at level 94, right associativity).
Infix    "≈"     := eqv        (at level 90, no associativity).

Declare Instance impl_reflexive : Reflexive impl.
Declare Instance impl_transitive : Transitive impl.

Program Instance eqv_equivalence : Equivalence eqv.
Next Obligation. intro x; now split. Qed.
Next Obligation. repeat intro; split; destruct H; now intuition. Qed.
Next Obligation. repeat intro; split; destruct H, H0; now transitivity y. Qed.

Program Instance impl_respects_impl : Proper (impl --> impl ==> Basics.impl) impl.
Next Obligation.
  repeat intro.
  unfold Basics.flip in H.
  rewrite H.
  now rewrite <- H0.
Qed.

Program Instance impl_respects_eqv : Proper (eqv ==> eqv ==> Basics.impl) impl.
Next Obligation.
  repeat intro.
  destruct H, H0.
  transitivity x; auto.
  transitivity x0; auto.
Qed.

Ltac one_arg :=
  repeat intro;
  match goal with
    [ H : _ ≈ _ |- _ ≈ _ ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    destruct H as [H1 H2]; split;
    first [ now rewrite H1
          | now rewrite H2 ]
  end.

Ltac two_arg :=
  repeat intro;
  match goal with
    [ HA : _ ≈ _, HB : _ ≈ _ |- _ ≈ _ ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    let H3 := fresh "H" in
    let H4 := fresh "H" in
    destruct HA as [H1 H2], HB as [H3 H4]; split;
    first [ now rewrite H1, H3
          | now rewrite H2, H4 ]
  end.

Obligation Tactic := solve [ one_arg | two_arg ].

Declare Instance not_respects_impl : Proper (impl --> impl) not | 1.
Program Instance not_respects_eqv : Proper (eqv ==> eqv) not.
Declare Instance or_respects_impl : Proper (impl ==> impl ==> impl) or.
Program Instance or_respects_eqv : Proper (eqv ==> eqv ==> eqv) or.

(** Implication must have the same meaning as in Coq's own logic. *)
Hypothesis impl_denote : forall (φ ψ : t), (φ ⟹ ψ) <-> (φ ≈ ⊤ -> ψ ≈ ⊤).

Hypothesis true_def : forall (φ : t), φ ∨ ¬φ ≈ ⊤.
Hypothesis false_def : forall (φ : t), ¬(φ ∨ ¬φ) ≈ ⊥.

(** This is one set of fundamental axioms of boolean algebra.
 *
 * NOTE: It is possible to formulate the following using a single axiom:
 *
 *   forall (φ ψ χ ρ : t),
 *     ¬(¬(¬(φ ∨ ψ) ∨ χ) ∨ ¬(φ ∨ ¬(¬χ ∨ ¬(χ ∨ ρ)))) ≈ χ
 *
 * However, the proofs of the three axioms below in terms of this single one
 * are laborious and left as an exercise to the motivated reader. Further
 * notes may be found in the paper "Short Single Axioms for Boolean Algebra"
 * by McCune, et al.
 *)
Hypothesis or_comm : forall (φ ψ : t), φ ∨ ψ ≈ ψ ∨ φ.
Hypothesis or_assoc : forall (φ ψ χ : t), (φ ∨ ψ) ∨ χ ≈ φ ∨ (ψ ∨ χ).
Hypothesis huntington : forall (φ ψ : t), ¬(¬φ ∨ ¬ψ) ∨ ¬(¬φ ∨ ψ) ≈ φ.

(** Many of the following proofs are based on work from:
    "A Complete Proof of the Robbins Conjecture", by Allen L. Mann
    May 25, 2003 *)
Theorem or_not (φ : t) : φ ∨ ¬φ ≈ ¬φ ∨ ¬¬φ.
Proof.
  pose proof (huntington φ (¬¬ φ)) as H1.
  pose proof (huntington (¬ φ) (¬¬ φ)) as H2.
  pose proof (huntington (¬ φ) (¬ φ)) as H3.
  pose proof (huntington (¬¬ φ) (¬ φ)) as H4.
  rewrite <- H4.
  rewrite <- H3 at 2.
  rewrite <- H2 at 1.
  rewrite <- H1 at 1.
  rewrite <- !or_assoc.
  rewrite (or_comm _ (¬ (¬ ¬ ¬ φ ∨ ¬ φ))).
  rewrite !or_assoc.
  apply or_respects_eqv.
    now rewrite or_comm.
  rewrite <- !or_assoc.
  rewrite (or_comm _ (¬ (¬ ¬ φ ∨ ¬ ¬ φ))).
  rewrite !or_assoc.
  apply or_respects_eqv.
    reflexivity.
  apply or_respects_eqv.
    now rewrite or_comm.
  now rewrite or_comm.
Qed.

Theorem not_not (φ : t) : ¬¬φ ≈ φ.
Proof.
  pose proof (huntington (¬¬ φ) (¬ φ)) as H1.
  pose proof (huntington φ (¬¬ φ)) as H2.
  rewrite <- H1.
  rewrite (or_comm _ (¬¬φ)), <- or_not.
  rewrite or_comm.
  rewrite (or_comm _ (¬φ)).
  now apply huntington.
Qed.

Theorem not_swap (φ ψ : t) : ¬φ ≈ ψ <-> φ ≈ ¬ψ.
Proof.
  split; intro.
  - rewrite <- not_not.
    now rewrite H.
  - rewrite H.
    now apply not_not.
Qed.

Theorem not_inj (φ ψ : t) : ¬φ ≈ ¬ψ -> φ ≈ ψ.
Proof.
  intro.
  rewrite <- (not_not φ).
  rewrite <- (not_not ψ).
  now rewrite H.
Qed.

Theorem not_true : ¬⊤ ≈ ⊥.
Proof. now rewrite <- (true_def ⊥), false_def. Qed.

Theorem not_false : ¬⊥ ≈ ⊤.
Proof.
  rewrite <- (false_def ⊤), true_def.
  now apply not_not.
Qed.

Theorem or_false (φ : t) : φ ∨ ⊥ ≈ φ.
Proof.
  pose proof (huntington ⊥ ⊥) as H1.
  rewrite (or_comm _ ⊥) in H1.
  rewrite false_def in H1.
  rewrite !not_false in H1.
  assert (H2 : ⊤ ∨ ¬(⊤ ∨ ⊤) ≈ ⊤).
    rewrite <- (true_def ⊤) at 1.
    rewrite or_assoc.
    rewrite (or_comm (¬⊤)).
    rewrite not_true at 1.
    rewrite H1.
    rewrite <- not_true.
    now apply true_def.
  assert (H3 : ⊤ ∨ ⊤ ≈ ⊤).
    rewrite <- H2 at 2.
    rewrite <- or_assoc.
    now apply true_def.
  assert (H4 : ⊥ ∨ ⊥ ≈ ⊥).
    rewrite <- not_true at 1.
    rewrite <- not_true at 1.
    rewrite <- H3 at 1.
    rewrite not_true.
    exact H1.
  rewrite <- (huntington φ φ) at 2.
  rewrite (or_comm _ φ).
  rewrite false_def.
  rewrite <- H4 at 2.
  rewrite <- (false_def φ) at 2.
  rewrite <- or_assoc.
  rewrite (or_comm φ (¬φ)).
  now rewrite huntington.
Qed.

Theorem false_or (φ : t) : ⊥ ∨ φ ≈ φ.
Proof. now rewrite or_comm; apply or_false. Qed.

Theorem or_idem (φ : t) : φ ∨ φ ≈ φ.
Proof.
  assert (H1 : forall φ, ¬ (¬ φ ∨ ¬ φ) ≈ φ).
    intro p.
    rewrite <- (huntington p p) at 3.
    rewrite (or_comm (¬p) p).
    rewrite false_def.
    now rewrite or_false.
  specialize (H1 (¬φ)).
  rewrite not_not in H1.
  apply not_inj.
  exact H1.
Qed.

Theorem or_true (φ : t) : φ ∨ ⊤ ≈ ⊤.
Proof.
  rewrite <- (true_def φ) at 1.
  rewrite <- or_assoc.
  rewrite or_idem.
  now apply true_def.
Qed.

Theorem true_or (φ : t) : ⊤ ∨ φ ≈ ⊤.
Proof. now rewrite or_comm; apply or_true. Qed.

Theorem not_not_or_true (φ : t) : ¬(¬φ ∨ ¬⊤) ≈ φ.
Proof.
  intros.
  rewrite not_true.
  rewrite or_false.
  now apply not_not.
Qed.

Theorem contrapositive (φ ψ : t) : φ ⟹ ψ <-> ¬ψ ⟹ ¬φ.
Proof.
  split; intro.
  - rewrite H.
    reflexivity.
  - apply not_respects_impl in H.
    now rewrite !not_not in H.
Qed.

Theorem impl_def : forall (φ ψ : t), (φ ⟹ ψ) <-> (⊤ ⟹ ¬ φ ∨ ψ).
Proof.
  split; intros.
  - rewrite <- H.
    rewrite or_comm.
    rewrite true_def.
    reflexivity.
  - apply impl_denote; intros.
    rewrite H0 in H.
    rewrite not_true in H.
    rewrite false_or in H.
    split; auto.
    clear.
    apply impl_denote; intros.
    reflexivity.
Qed.

Theorem or_inj (φ ψ : t) : φ ⟹ φ ∨ ψ.
Proof.
  apply impl_def.
  rewrite <- or_assoc.
  rewrite (or_comm _ φ).
  rewrite true_def.
  rewrite true_or.
  reflexivity.
Qed.

Theorem true_impl (φ : t) : ⊤ ⟹ φ <-> φ ≈ ⊤.
Proof.
  split; intro.
  - split; auto.
    rewrite <- (true_def φ).
    now apply or_inj.
  - now rewrite H.
Qed.

Theorem excluded_middle (φ : t) : ⊤ ⟹ φ ∨ ¬φ.
Proof.
  apply true_impl.
  now rewrite <- true_def.
Qed.

Theorem impl_true (φ : t) : φ ⟹ ⊤.
Proof.
  rewrite <- (true_def φ).
  now apply or_inj.
Qed.

Theorem false_impl (φ : t) : ⊥ ⟹ φ.
Proof.
  rewrite <- (false_def φ).
  apply contrapositive.
  rewrite not_not.
  rewrite or_comm.
  now apply or_inj.
Qed.

End MinimalBooleanLogic.
