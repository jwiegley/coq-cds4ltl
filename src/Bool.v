Require Import
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid
  MinBool.

(***********************************************************************
 * This Boolean Logic adds the concept of ∧, which although it can be
 * defined simply in terms of ∨, this allows for more optimal choices
 * if meant to be used computationally.
 *)

Module Type BooleanLogic.

Declare Module MinBool : MinimalBooleanLogic.
Include MinBool.

Parameter and : t -> t -> t.

Infix    "∧"       := and             (at level 45, right associativity).
Notation "p ↔ q"   := (p → q ∧ q → p) (at level 80, right associativity, only parsing).
Notation "p ≡ q"   := (p ↔ q)         (at level 80, right associativity, only parsing).

Declare Instance and_respects_impl : Proper (impl ==> impl ==> impl) and.
Program Instance and_respects_eqv : Proper (eqv ==> eqv ==> eqv) and.

(** "and" is not fundamental, and can be defined in terms of "or". To allow
    for efficient choices of "and", we simply require that its behavior be
    equivalent to the more basic definition. *)
Hypothesis and_def : forall (φ ψ : t), φ ∧ ψ ≈ ¬(¬φ ∨ ¬ψ).

Lemma and_or (φ ψ χ : t) : φ ∧ (ψ ∨ χ) ≈ (φ ∧ ψ) ∨ (φ ∧ χ).
Proof.
  rewrite !and_def.
  apply not_swap.
  rewrite or_distr_not.
  now rewrite !not_not.
Qed.

Lemma or_and (φ ψ χ : t) : φ ∨ (ψ ∧ χ) ≈ (φ ∨ ψ) ∧ (φ ∨ χ).
Proof.
  rewrite !and_def.
  now rewrite or_distr_not.
Qed.

Lemma absurdity (φ : t) : φ ∧ ¬φ ≈ ⊥.
Proof.
  rewrite and_def.
  now rewrite <- false_def.
Qed.

Lemma not_or (φ ψ : t) : ¬(φ ∨ ψ) ≈ ¬φ ∧ ¬ψ.
Proof.
  rewrite and_def.
  now rewrite !not_not.
Qed.

Lemma not_and (φ ψ : t) : ¬(φ ∧ ψ) ≈ ¬φ ∨ ¬ψ.
Proof.
  rewrite and_def.
  now rewrite !not_not.
Qed.

Lemma and_true (φ : t) : φ ∧ ⊤ ≈ φ.
Proof.
  rewrite and_def.
  rewrite not_true.
  rewrite or_false.
  now apply not_not.
Qed.

Lemma and_false (φ : t) : φ ∧ ⊥ ≈ ⊥.
Proof.
  rewrite and_def.
  rewrite not_false.
  rewrite or_true.
  now apply not_true.
Qed.

Lemma true_and (φ : t) : ⊤ ∧ φ ≈ φ.
Proof.
  rewrite and_def.
  rewrite not_true.
  rewrite false_or.
  now apply not_not.
Qed.

Lemma false_and (φ : t) : ⊥ ∧ φ ≈ ⊥.
Proof.
  rewrite and_def.
  rewrite not_false.
  rewrite true_or.
  now apply not_true.
Qed.

Lemma and_idem (φ : t) : φ ∧ φ ≈ φ.
Proof.
  rewrite and_def.
  rewrite or_idem.
  now apply not_not.
Qed.

Lemma and_comm (φ ψ : t) : φ ∧ ψ ≈ ψ ∧ φ.
Proof.
  rewrite !and_def.
  now rewrite or_comm.
Qed.

Lemma and_assoc (φ ψ χ : t) : (φ ∧ ψ) ∧ χ ≈ φ ∧ (ψ ∧ χ).
Proof.
  rewrite !and_def.
  rewrite !not_not.
  now rewrite or_assoc.
Qed.

Lemma or_absorb (φ ψ : t) : φ ∨ (φ ∧ ψ) ≈ φ.
Proof.
  rewrite <- (and_true φ) at 1.
  rewrite <- and_or.
  rewrite or_comm.
  rewrite or_true.
  now rewrite and_true.
Qed.

Lemma and_absorb (φ ψ : t) : φ ∧ (φ ∨ ψ) ≈ φ.
Proof.
  rewrite <- (or_false φ) at 1.
  rewrite <- or_and.
  rewrite and_comm.
  rewrite and_false.
  now rewrite or_false.
Qed.

Lemma and_proj (φ ψ : t) : φ ∧ ψ ⟹ φ.
Proof.
  apply impl_eqv_denote.
  rewrite and_def.
  rewrite or_comm.
  rewrite not_not.
  rewrite <- or_assoc.
  rewrite true_def.
  now rewrite true_or.
Qed.

Ltac boolean :=
  repeat match goal with
    | [ |- context G [¬ ⊤] ] => rewrite not_true
    | [ |- context G [¬ ⊥] ] => rewrite not_false
    | [ |- context G [¬¬ ?P] ] => rewrite (not_not P)
    | [ |- context G [?P ∧ ?P] ] => rewrite (and_idem P)
    | [ |- context G [?P ∨ ?P] ] => rewrite (or_idem P)
    | [ |- context G [⊤ ∧ ?P] ] => rewrite true_and
    | [ |- context G [?P ∧ ⊤] ] => rewrite and_true
    | [ |- context G [⊥ ∧ ?P] ] => rewrite false_and
    | [ |- context G [?P ∧ ⊥] ] => rewrite and_false
    | [ |- context G [⊤ ∨ ?P] ] => rewrite true_or
    | [ |- context G [?P ∨ ⊤] ] => rewrite or_true
    | [ |- context G [⊥ ∨ ?P] ] => rewrite false_or
    | [ |- context G [?P ∨ ⊥] ] => rewrite or_false
    | [ |- context G [¬ ?P ∨ ?P] ] => rewrite (or_comm (¬ P) P)
    | [ |- context G [?P ∨ ¬ ?P] ] => rewrite true_def
    | [ |- context G [(¬ ?P ∨ ?Q) ∧ ?P] ] =>
        rewrite (and_comm (¬ P ∨ Q) P),
                (and_or P (¬ P) Q), and_def
    | [ |- context G [¬ ?P ∧ ?P] ] => rewrite (and_comm (¬ P) P)
    | [ |- context G [?P ∧ ¬ ?P] ] => rewrite (absurdity P)
    | [ |- context G [?P ∨ (?P ∧ ?Q)] ] => rewrite (or_absorb P Q)
    | [ |- context G [?P ∧ (?P ∨ ?Q)] ] => rewrite (and_absorb P Q)
    | [ |- ?P ≈ ?P ] => reflexivity
    | [ |- ?P ⟹ ?P ] => reflexivity
    | [ |- ?P ⟹ ⊤ ] => apply impl_true
    | [ |- ⊥ ⟹ ?P ] => apply false_impl
    | [ |- ?P ∧ ?Q ⟹ ?P ] => apply and_proj
    | [ |- ?Q ∧ ?P ⟹ ?P ] => rewrite (and_comm Q P)
    | [ |- ?P ⟹ ?P ∨ ?Q ] => apply or_inj
    | [ |- ?P ⟹ ?Q ∨ ?P ] => rewrite (or_comm Q P)
    | [ |- ?P ∨ ?Q ≈ ?Q ∨ ?P ] => apply or_comm
    | [ |- ?P ∧ ?Q ≈ ?Q ∧ ?P ] => apply and_comm
    | [ |- ?P ∨ ?Q ⟹ ?Q ∨ ?P ] => rewrite (or_comm P Q)
    | [ |- ?P ∧ ?Q ⟹ ?Q ∧ ?P ] => rewrite (and_comm P Q)
  end.

Lemma impl_and (φ ψ χ : t) : φ ∧ ψ → χ ≈ φ → (ψ → χ).
Proof.
  rewrite and_def.
  rewrite not_not.
  now rewrite <- or_assoc.
Qed.

Lemma and_impl (φ ψ : t) : φ ∧ (φ → ψ) ≈ φ ∧ ψ.
Proof. now rewrite and_or; boolean. Qed.

Lemma and_impl_iff (φ ψ χ : t) : φ ∧ ψ ⟹ χ <-> φ ⟹ (ψ → χ).
Proof.
  split; intro.
  - rewrite <- H; clear H.
    rewrite and_comm.
    rewrite or_and.
    now boolean.
  - rewrite H; clear H.
    rewrite and_comm.
    rewrite and_or.
    now boolean.
Qed.

Lemma impl_trans (φ ψ χ : t) : (φ → ψ) ∧ (ψ → χ) ⟹ (φ → χ).
Proof.
  apply and_impl_iff.
  rewrite (or_comm _ (_ ∨ _)).
  rewrite or_assoc.
  apply or_respects_impl; [reflexivity|].
  rewrite or_comm.
  rewrite not_or.
  rewrite not_not.
  rewrite or_comm.
  rewrite or_and.
  now boolean.
Qed.

End BooleanLogic.
