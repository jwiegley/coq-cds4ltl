Set Warnings "-local-declaration".

Require Import
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid
  MinBool.

(***********************************************************************
 * This Boolean Logic adds the concept of ∧, which although it can be
 * defined simply in terms of ∨, this allows for more optimal choices
 * if meant to be used computationally. *)

Module Type BooleanLogic.

Include MinimalBooleanLogic.

Parameter and : t -> t -> t.

Infix    "∧"       := and             (at level 80, right associativity) : boolean_scope.
Notation "p ≡ q"   := (p ⇒ q ∧ q ⇒ p) (at level 89, right associativity, only parsing) : boolean_scope.

Declare Instance and_respects_impl : Proper (impl ==> impl ==> impl) and.
Program Instance and_respects_eqv : Proper (eqv ==> eqv ==> eqv) and.

(** "and" is not fundamental and can be defined using "or". To allow for
    efficient choices of "and", we simply require that its behavior be
    equivalent to the more basic definition. *)
Axiom and_def : forall (φ ψ : t), φ ∧ ψ ≈ ¬(¬φ ∨ ¬ψ).

Theorem not_or (φ ψ : t) : ¬(φ ∨ ψ) ≈ ¬φ ∧ ¬ψ.
Proof.
  rewrite and_def.
  now rewrite !not_not.
Qed.

Theorem not_and (φ ψ : t) : ¬(φ ∧ ψ) ≈ ¬φ ∨ ¬ψ.
Proof.
  rewrite and_def.
  now rewrite !not_not.
Qed.

Theorem or_def (φ ψ : t) : φ ∨ ψ ≈ ¬(¬φ ∧ ¬ψ).
Proof.
  rewrite <- (not_not (φ ∨ ψ)).
  now rewrite not_or.
Qed.

Theorem and_true (φ : t) : φ ∧ ⊤ ≈ φ.
Proof.
  rewrite and_def.
  rewrite not_true.
  rewrite or_false.
  now apply not_not.
Qed.

Theorem and_false (φ : t) : φ ∧ ⊥ ≈ ⊥.
Proof.
  rewrite and_def.
  rewrite not_false.
  rewrite or_true.
  now apply not_true.
Qed.

Theorem true_and (φ : t) : ⊤ ∧ φ ≈ φ.
Proof.
  rewrite and_def.
  rewrite not_true.
  rewrite false_or.
  now apply not_not.
Qed.

Theorem false_and (φ : t) : ⊥ ∧ φ ≈ ⊥.
Proof.
  rewrite and_def.
  rewrite not_false.
  rewrite true_or.
  now apply not_true.
Qed.

Theorem and_idem (φ : t) : φ ∧ φ ≈ φ.
Proof.
  rewrite and_def.
  rewrite or_idem.
  now apply not_not.
Qed.

Theorem and_comm (φ ψ : t) : φ ∧ ψ ≈ ψ ∧ φ.
Proof.
  rewrite !and_def.
  now rewrite or_comm.
Qed.

Theorem and_assoc (φ ψ χ : t) : (φ ∧ ψ) ∧ χ ≈ φ ∧ (ψ ∧ χ).
Proof.
  rewrite !and_def.
  rewrite !not_not.
  now rewrite or_assoc.
Qed.

Theorem or_absorb (φ ψ : t) : φ ∨ (φ ∧ ψ) ≈ φ.
Proof.
  rewrite <- (huntington φ ψ) at 1.
  rewrite and_def.
  rewrite <- (or_comm (¬(¬φ ∨ ¬ψ))).
  rewrite <- or_assoc.
  rewrite or_idem.
  now apply huntington.
Qed.

Theorem and_absorb (φ ψ : t) : φ ∧ (φ ∨ ψ) ≈ φ.
Proof.
  rewrite and_def.
  rewrite <- (not_not φ) at 2.
  rewrite <- (not_not ψ).
  rewrite <- (and_def (¬φ)).
  rewrite or_absorb.
  now rewrite not_not.
Qed.

Theorem and_this_not_that (φ ψ : t) : (φ ∧ ψ) ∨ (φ ∧ ¬ψ) ≈ φ.
Proof.
  rewrite !and_def.
  rewrite not_not.
  now apply huntington.
Qed.

Theorem absurdity (φ : t) : φ ∧ ¬φ ≈ ⊥.
Proof.
  rewrite and_def.
  now rewrite <- false_def.
Qed.

(** This proof was discovered by Don Monk. *)
Theorem and_or (φ ψ χ : t) : φ ∧ (ψ ∨ χ) ≈ (φ ∧ ψ) ∨ (φ ∧ χ).
Proof.
  rewrite <- (and_this_not_that (φ ∧ (ψ ∨ χ)) ψ).
  rewrite !and_assoc.
  rewrite (and_comm _ ψ).
  rewrite and_absorb.
  rewrite <- (and_this_not_that (φ ∧ ψ) χ) at 1.
  rewrite <- (and_this_not_that (φ ∧ (ψ ∨ χ) ∧ ¬ψ) χ).
  rewrite (and_assoc φ ((ψ ∨ χ) ∧ ¬ψ) χ).
  rewrite (and_comm ((ψ ∨ χ) ∧ ¬ψ) χ).
  rewrite (or_comm ψ χ) at 1.
  rewrite <- (and_assoc χ (χ ∨ ψ)).
  rewrite and_absorb.
  rewrite !and_assoc.
  rewrite <- not_or.
  rewrite absurdity.
  rewrite and_false.
  rewrite or_false.
  rewrite (and_comm χ (¬ψ)).
  rewrite <- (or_idem (φ ∧ ψ ∧ χ)).
  rewrite !or_assoc.
  rewrite (or_comm (φ ∧ ψ ∧ χ)).
  rewrite !or_assoc.
  rewrite (or_comm _ (φ ∧ ψ ∧ χ)).
  rewrite <- or_assoc.
  rewrite <- and_assoc.
  rewrite <- and_assoc.
  rewrite and_this_not_that.
  rewrite and_assoc.
  rewrite !(and_comm _ χ).
  rewrite <- and_assoc.
  rewrite <- and_assoc.
  rewrite and_this_not_that.
  now rewrite (and_comm _ χ).
Qed.

Theorem and_or_r (φ ψ χ : t) : (ψ ∨ χ) ∧ φ ≈ (ψ ∧ φ) ∨ (χ ∧ φ).
Proof.
  rewrite and_comm.
  rewrite and_or.
  rewrite !(and_comm φ).
  reflexivity.
Qed.

Theorem or_and (φ ψ χ : t) : φ ∨ (ψ ∧ χ) ≈ (φ ∨ ψ) ∧ (φ ∨ χ).
Proof.
  rewrite <- (not_not φ) at 1.
  rewrite and_def.
  rewrite <- (not_not (¬¬φ ∨ ¬(¬ψ ∨ ¬χ))).
  rewrite <- and_def.
  rewrite and_or.
  rewrite <- !not_or.
  now rewrite <- and_def.
Qed.

Theorem or_and_r (φ ψ χ : t) : (ψ ∧ χ) ∨ φ ≈ (ψ ∨ φ) ∧ (χ ∨ φ).
Proof.
  rewrite or_comm.
  rewrite or_and.
  rewrite !(or_comm φ).
  reflexivity.
Qed.

Theorem or_not_absorb (φ ψ : t) : φ ∨ (¬φ ∧ ψ) ≈ φ ∨ ψ.
Proof.
  rewrite or_and.
  rewrite true_def.
  now rewrite true_and.
Qed.

Theorem and_not_absorb (φ ψ : t) : φ ∧ (¬φ ∨ ψ) ≈ φ ∧ ψ.
Proof.
  rewrite and_or.
  rewrite absurdity.
  now rewrite false_or.
Qed.

Theorem and_proj (φ ψ : t) : φ ∧ ψ ⟹ φ.
Proof.
  apply impl_def.
  rewrite and_def.
  rewrite not_not.
  rewrite or_comm.
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

Theorem and_impl (φ ψ χ : t) : φ ∧ ψ ⇒ χ ≈ φ ⇒ (ψ ⇒ χ).
Proof.
  rewrite and_def.
  rewrite not_not.
  now rewrite <- or_assoc.
Qed.

Theorem impl_and (φ ψ χ : t) : φ ⇒ ψ ∧ χ ≈ (φ ⇒ ψ) ∧ (φ ⇒ χ).
Proof. now rewrite <- or_and. Qed.

Theorem or_impl (φ ψ χ : t) : φ ∨ ψ ⇒ χ ≈ (φ ⇒ χ) ∧ (ψ ⇒ χ).
Proof.
  rewrite !(or_comm _ χ).
  rewrite <- or_and.
  rewrite and_def.
  now rewrite !not_not.
Qed.

Theorem and_apply (φ ψ : t) : φ ∧ (φ ⇒ ψ) ≈ φ ∧ ψ.
Proof. now rewrite and_or; boolean. Qed.

Theorem and_impl_iff (φ ψ χ : t) : (φ ∧ ψ ⟹ χ) <-> (φ ⟹ (ψ ⇒ χ)).
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

Theorem impl_trans (φ ψ χ : t) : (φ ⇒ ψ) ∧ (ψ ⇒ χ) ⟹ (φ ⇒ χ).
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

Theorem impl_apply (φ ψ : t) : (φ ⇒ ψ) ∧ φ ≈ φ ∧ ψ.
Proof. now boolean. Qed.

Theorem or_impl_iff (φ ψ χ : t) : (φ ∨ ψ ⟹ χ) <-> (φ ⇒ χ) ∧ (ψ ⇒ χ) ≈ ⊤.
Proof.
  split; intros.
  - rewrite !(or_comm _ χ).
    rewrite <- or_and.
    rewrite and_def.
    rewrite !not_not.
    split.
    + now apply impl_true.
    + rewrite <- H at 1.
      now rewrite true_def.
  - rewrite !(or_comm _ χ) in H.
    rewrite <- or_and in H.
    rewrite and_def in H.
    rewrite !not_not in H.
    rewrite or_comm in H.
    apply impl_def.
    now rewrite H.
Qed.

Theorem impl_iff (φ ψ : t) : (φ ⟹ ψ) <-> (φ ⇒ ψ ≈ ⊤).
Proof.
  split; intro.
  - apply true_impl.
    rewrite <- H.
    now boolean.
  - apply impl_def.
    now rewrite <- H.
Qed.

Theorem or_excl_middle (φ ψ : t) : φ ∨ ψ ≈ φ ∨ (¬ φ ∧ ψ).
Proof.
  rewrite or_and.
  now boolean.
Qed.

Theorem or_monotonicity (φ ψ χ : t) : (φ ⇒ ψ) ⟹ (φ ∨ χ ⇒ ψ ∨ χ).
Proof.
  rewrite not_or.
  rewrite <- or_assoc.
  rewrite !or_and_r.
  rewrite !(or_comm _ χ).
  rewrite <- !or_assoc.
  boolean.
  rewrite (or_comm χ).
  now rewrite <- (or_inj _ χ).
Qed.

Theorem or_and_or (φ ψ χ ρ : t) :
  (φ ∨ ψ) ∧ (χ ∨ ρ) ≈ (φ ∧ χ) ∨ (φ ∧ ρ) ∨ (χ ∧ ψ) ∨ (ρ ∧ ψ).
Proof.
  rewrite and_or.
  rewrite !and_or_r.
  rewrite !or_assoc.
  apply or_respects_eqv; [reflexivity|].
  rewrite <- !or_assoc.
  apply or_respects_eqv; [|now boolean].
  rewrite or_comm.
  now apply or_respects_eqv; boolean.
Qed.

Theorem and_or_and (φ ψ χ ρ : t) :
  (φ ∧ ψ) ∨ (χ ∧ ρ) ≈ (φ ∨ χ) ∧ (φ ∨ ρ) ∧ (χ ∨ ψ) ∧ (ρ ∨ ψ).
Proof.
  rewrite or_and.
  rewrite !or_and_r.
  rewrite !and_assoc.
  apply and_respects_eqv; [reflexivity|].
  rewrite <- !and_assoc.
  apply and_respects_eqv; [|now boolean].
  rewrite and_comm.
  now apply and_respects_eqv; boolean.
Qed.

Theorem or_eqv_impl (p q : t) : (p ∨ q ≈ q) <-> (p ⟹ q).
Proof.
  split; intro.
  - destruct H.
    now rewrite <- H; boolean.
  - split.
    + rewrite H.
      now boolean.
    + now boolean.
Qed.

Theorem and_eqv_impl (p q : t) : (p ∧ q ≈ p) <-> (p ⟹ q).
Proof.
  split; intro.
  - destruct H.
    now rewrite H0; boolean.
  - split.
    + now boolean.
    + rewrite <- H.
      now boolean.
Qed.

Theorem impl_refl (p : t) : p ⇒ p ≈ ⊤.
Proof. now boolean. Qed.

End BooleanLogic.
