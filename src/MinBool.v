Require Import
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid.

(***********************************************************************
 * This is a minimal Boolean Logic comprised of ∨, ¬ and five axioms.
 *
 * NOTE: It is possible to formulate the following using a single axiom:
 *
 *   forall (φ ψ χ ρ : t),
 *     ¬(¬(¬(φ ∨ ψ) ∨ χ) ∨ ¬(φ ∨ ¬(¬χ ∨ ¬(χ ∨ ρ)))) ≈ χ
 *
 * However, the proofs of the five axioms below in terms of this single one
 * are laborious and left as an exercise to the motivated reader. Further
 * notes may be found in the paper "Short Single Axioms for Boolean Algebra"
 * by McCune, et al.: https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf
 *)

Module Type MinimalBooleanLogic.

Parameter t : Type.

Parameter not : t -> t.
Parameter or : t -> t -> t.
Parameter true : t.
Parameter false : t.
Parameter impl : t -> t -> Prop.

Declare Instance impl_reflexive : Reflexive impl.
Declare Instance impl_transitive : Transitive impl.

Declare Instance not_respects_impl :
  Proper (impl --> impl) not | 1.
Declare Instance or_respects_impl :
  Proper (impl ==> impl ==> impl) or.

Definition eqv (x y : t) : Prop := impl x y /\ impl y x.

Program Instance eqv_equivalence : Equivalence eqv.
Next Obligation. intro x; now split. Qed.
Next Obligation. repeat intro; split; destruct H; now intuition. Qed.
Next Obligation. repeat intro; split; destruct H, H0; now transitivity y. Qed.

Program Instance impl_respects_eqv :
  Proper (eqv ==> eqv ==> Basics.impl) impl.
Next Obligation.
  repeat intro.
  destruct H, H0.
  transitivity x; auto.
  transitivity x0; auto.
Qed.

Program Instance not_respects_eqv :
  Proper (eqv ==> eqv) not.
Next Obligation.
  repeat intro.
  destruct H; split.
  - now rewrite H0.
  - now rewrite H.
Qed.

Program Instance or_respects_eqv :
  Proper (eqv ==> eqv ==> eqv) or.
Next Obligation.
  repeat intro.
  destruct H, H0; split.
  - now rewrite H, H0.
  - now rewrite H1, H2.
Qed.

Notation "¬ p"   := (not p)    (at level 0, right associativity).
Infix    "∨"     := or         (at level 46, right associativity).
Notation "p → q" := (¬ p ∨ q)  (at level 51, right associativity, only parsing).
Notation "⊤"     := true       (at level 0, no associativity).
Notation "⊥"     := false      (at level 0, no associativity).
Infix    "⟹"    := impl       (at level 94, right associativity).
Infix    "≈"     := eqv        (at level 90, no associativity).

Hypothesis impl_def : forall (φ ψ : t), φ ⟹ ψ <-> φ → ψ ≈ ⊤.
Hypothesis true_def : forall (φ : t), φ ∨ ¬ φ ≈ ⊤.
Hypothesis false_def : forall (φ : t), ¬ (φ ∨ ¬ φ) ≈ ⊥.

(** This is one set of fundamental axioms of boolean algebra.
    "and" is not fundamental, and can be defined in terms of "or". *)
Hypothesis or_true : forall (φ : t), φ ∨ ⊤ ≈ ⊤.
Hypothesis or_false : forall (φ : t), φ ∨ ⊥ ≈ φ.
Hypothesis or_comm : forall (φ ψ : t), φ ∨ ψ ≈ ψ ∨ φ.
Hypothesis or_assoc : forall (φ ψ χ : t), (φ ∨ ψ) ∨ χ ≈ φ ∨ (ψ ∨ χ).
Hypothesis or_distr_not : forall (φ ψ χ : t),
  ¬ (¬ (φ ∨ ψ) ∨ ¬ (φ ∨ χ)) ≈ φ ∨ ¬ (¬ ψ ∨ ¬ χ).

Lemma true_or (φ : t) : ⊤ ∨ φ ≈ ⊤.
Proof. now rewrite or_comm; apply or_true. Qed.

Lemma false_or (φ : t) : ⊥ ∨ φ ≈ φ.
Proof. now rewrite or_comm; apply or_false. Qed.

Lemma not_true : ¬ ⊤ ≈ ⊥.
Proof. now rewrite <- (true_def ⊥), false_def. Qed.
Lemma not_false : ¬ ⊥ ≈ ⊤.
Proof. now rewrite <- (true_def ⊥), false_or. Qed.

Lemma not_not (φ : t) : ¬¬ φ ≈ φ.
Proof.
  intros.
  rewrite <- or_false.
  rewrite <- (or_false φ) at 2.
  rewrite <- not_true at 2.
  rewrite <- (or_false ⊤).
  rewrite <- not_true at 2.
  rewrite <- not_false at 1.
  rewrite <- (or_distr_not φ ⊥ ⊤).
  rewrite !or_false.
  rewrite or_true.
  rewrite not_true.
  now rewrite or_false.
Qed.

Lemma not_not_or (φ : t) : ¬ (¬ φ ∨ ¬ ⊤) ≈ φ.
Proof.
  intros.
  rewrite not_true.
  rewrite or_false.
  now apply not_not.
Qed.

Lemma or_idem (φ : t) : φ ∨ φ ≈ φ.
Proof.
  intros.
  rewrite <- (or_false φ) at 3.
  rewrite <- (false_def φ).
  rewrite <- (not_not φ) at 4.
  rewrite <- or_distr_not.
  rewrite true_def.
  rewrite not_true.
  rewrite false_or.
  now rewrite not_not.
Qed.

Lemma impl_true (φ : t) : ⊤ ⟹ φ <-> φ ≈ ⊤.
Proof.
  split; intro.
  - apply impl_def in H.
    rewrite not_true in H.
    now rewrite false_or in H.
  - apply impl_def.
    rewrite not_true.
    now rewrite false_or.
Qed.

Lemma excluded_middle (φ : t) : ⊤ ⟹ φ ∨ ¬ φ.
Proof.
  apply impl_true.
  now rewrite <- true_def.
Qed.

Lemma contrapositive (φ ψ : t) : φ ⟹ ψ <-> ¬ ψ ⟹ ¬ φ.
Proof.
  split; intro.
  - apply impl_def in H.
    apply impl_def.
    rewrite not_not.
    now rewrite or_comm.
  - apply impl_def in H.
    apply impl_def.
    rewrite or_comm.
    now rewrite not_not in H.
Qed.

Lemma or_inj (φ ψ : t) : φ ⟹ φ ∨ ψ.
Proof.
  apply impl_def.
  rewrite <- or_assoc.
  rewrite (or_comm _ φ).
  rewrite true_def.
  now apply true_or.
Qed.

Lemma not_swap (φ ψ : t) : ¬ φ ≈ ψ <-> φ ≈ ¬ ψ.
Proof.
  split; intro.
  - rewrite <- not_not.
    now rewrite H.
  - rewrite H.
    now apply not_not.
Qed.

End MinimalBooleanLogic.
