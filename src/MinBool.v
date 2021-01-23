Require Import
  Coq.Classes.Morphisms
  Impl.

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

Declare Module Impl : Implication.
Include Impl.

Parameter not : t -> t.
Parameter or : t -> t -> t.
Parameter true : t.
Parameter false : t.

Declare Instance not_impl_Proper : Proper (impl --> impl) not | 1.
Declare Instance not_equiv_Proper : Proper (equiv ==> equiv) not.
Declare Instance or_impl_Proper : Proper (impl ==> impl ==> impl) or | 1.
Declare Instance or_equiv_Proper : Proper (equiv ==> equiv ==> equiv) or.

Notation "¬ p"   := (not p)   (at level 0).
Infix    "∨"     := or        (at level 46, right associativity).
Notation "p → q" := (¬ p ∨ q) (at level 80, only parsing).
Notation "⊤"     := true      (at level 0).
Notation "⊥"     := false     (at level 0).
Notation "p ⟹ q" := (p → q ≈ ⊤) (at level 50, only parsing).

Hypothesis impl_def : forall (φ ψ : t), φ ⟹ ψ <-> φ → ψ ≈ ⊤.
Hypothesis true_def : forall (φ : t), ⊤ ≈ φ ∨ ¬ φ.
Hypothesis false_def : forall (φ : t), ⊥ ≈ ¬ (φ ∨ ¬ φ).

(** This is one set of fundamental axioms of boolean algebra.
    "and" is not fundamental, and can be defined in terms of "or". *)
Hypothesis or_true : forall (φ : t), φ ∨ ⊤ ≈ ⊤.
Hypothesis or_false : forall (φ : t), φ ∨ ⊥ ≈ φ.
Hypothesis or_comm : forall (φ ψ : t), φ ∨ ψ ≈ ψ ∨ φ.
Hypothesis or_assoc : forall (φ ψ χ : t), (φ ∨ ψ) ∨ χ ≈ φ ∨ (ψ ∨ χ).
Hypothesis or_distr_not : forall (φ ψ χ : t),
  ¬ (¬ (φ ∨ ψ) ∨ ¬ (φ ∨ χ)) ≈ φ ∨ ¬ (¬ ψ ∨ ¬ χ).

Lemma not_true : ¬ ⊤ ≈ ⊥.
Proof.
  rewrite (true_def ⊥).
  now rewrite <- false_def.
Qed.

Lemma not_false : ¬ ⊥ ≈ ⊤.
Proof.
  rewrite (true_def ⊥).
  rewrite or_comm.
  now rewrite or_false.
Qed.

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
  rewrite (false_def φ).
  rewrite <- (not_not φ) at 4.
  rewrite <- or_distr_not.
  rewrite <- true_def.
  rewrite not_true.
  rewrite (or_comm ⊥).
  rewrite or_false.
  now rewrite not_not.
Qed.

Lemma impl_true (φ : t) : ⊤ ⟹ φ <-> φ ≈ ⊤.
Proof.
  split; intro.
  - rewrite not_true in H.
    rewrite or_comm in H.
    now rewrite or_false in H.
  - rewrite not_true.
    rewrite or_comm.
    now rewrite or_false
Qed.

Proof.
  split; intro.
  - apply impl_def in H.
    rewrite <- H.
    rewrite not_true.
    rewrite or_comm.
    now rewrite or_false.
  - apply impl_def.
    rewrite <- H at 1.
    rewrite or_comm.
    now rewrite <- true_def.
Qed.

Lemma excluded_middle (φ : t) : ⊤ ⟹ φ ∨ ¬ φ.
Proof.
  apply impl_true.
  now rewrite <- true_def.
Qed.

(*
Lemma or_split_true (φ ψ : t) : φ ∨ ψ ≈ ⊤ <-> (φ ≈ ⊤) \/ (ψ ≈ ⊤).
Proof.
  split; intro.
  - apply equiv_def in H.
    destruct H.
    pose proof (excluded_middle φ).

Lemma or_split_false (φ ψ : t) : φ ∨ ψ ≈ ⊥ <-> (φ ≈ ⊥) /\ (ψ ≈ ⊥).
*)

Lemma contrapositive (φ ψ : t) : φ ⟹ ψ <-> ¬ ψ ⟹ ¬ φ.
Proof.
  split; intro.
  - apply impl_def.
    rewrite not_not.
    rewrite or_comm.
    now apply (proj1 (impl_def _ _)).
  - apply impl_def.
    rewrite or_comm.
    apply impl_def in H.
    now rewrite not_not in H.
Qed.

Lemma or_inj (φ ψ : t) : φ ⟹ φ ∨ ψ.
Proof.
  apply impl_def.
  rewrite <- or_assoc.
  rewrite (or_comm _ φ).
  rewrite <- true_def.
  rewrite or_comm.
  now apply or_true.
Qed.

Lemma not_swap (φ ψ : t) : (¬ φ ≈ ψ) <-> (φ ≈ ¬ ψ).
Proof.
  split; intro.
  - rewrite <- not_not.
    now rewrite H.
  - rewrite H.
    now apply not_not.
Qed.

(*
Lemma or_distr_impl (φ ψ χ : t) : φ ∨ ψ ⟹ χ <-> (φ → χ) ∧ (ψ → χ) ≈ ⊤.


Lemma impl_distr_or (φ ψ χ : t) : φ ⟹ ψ ∨ χ <-> (φ → ψ) ∨ (φ → χ) ≈ ⊤.
Proof.

Lemma impl_or (φ ψ χ : t) : φ ⟹ ψ ∨ χ <-> (φ ⟹ ψ) /\ (ψ ⟹ χ).
*)

End MinimalBooleanLogic.
