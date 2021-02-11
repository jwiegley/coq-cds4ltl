Set Warnings "-local-declaration".

Require Import
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid
  MinBool.

(***********************************************************************
 * This Boolean Logic adds the concept of ∧, which although it can be
 * defined simply in terms of ∨, this allows for more optimal choices
 * if meant to be used computationally. *)

Module Type BooleanLogic <: MinimalBooleanLogic.

Include MinimalBooleanLogic.

Parameter and : t -> t -> t.

Infix    "∧"       := and             (at level 80, right associativity) : boolean_scope.
Notation "p ≡ q"   := (p ⇒ q ∧ q ⇒ p) (at level 89, right associativity, only parsing) : boolean_scope.

Declare Instance and_respects_impl : Proper (impl ==> impl ==> impl) and.

(** "and" is not fundamental and can be defined using "or". To allow for
    efficient choices of "and", we simply require that its behavior be
    equivalent to the more basic definition. *)
Axiom and_def : forall (p q : t), p ∧ q ≈ ¬(¬p ∨ ¬q).

End BooleanLogic.

Module BooleanLogicFacts (B : BooleanLogic).

Import B.
Module Import MBF := MinimalBooleanLogicFacts B.

Program Instance and_respects_eqv : Proper (eqv ==> eqv ==> eqv) and.

Theorem not_or (p q : t) : ¬(p ∨ q) ≈ ¬p ∧ ¬q.
Proof.
  rewrite and_def.
  now rewrite !not_not.
Qed.

Theorem not_and (p q : t) : ¬(p ∧ q) ≈ ¬p ∨ ¬q.
Proof.
  rewrite and_def.
  now rewrite !not_not.
Qed.

Theorem or_def (p q : t) : p ∨ q ≈ ¬(¬p ∧ ¬q).
Proof.
  rewrite <- (not_not (p ∨ q)).
  now rewrite not_or.
Qed.

Theorem and_true (p : t) : p ∧ ⊤ ≈ p.
Proof.
  rewrite and_def.
  rewrite not_true.
  rewrite or_false.
  now apply not_not.
Qed.

Theorem and_false (p : t) : p ∧ ⊥ ≈ ⊥.
Proof.
  rewrite and_def.
  rewrite not_false.
  rewrite or_true.
  now apply not_true.
Qed.

Theorem true_and (p : t) : ⊤ ∧ p ≈ p.
Proof.
  rewrite and_def.
  rewrite not_true.
  rewrite false_or.
  now apply not_not.
Qed.

Theorem false_and (p : t) : ⊥ ∧ p ≈ ⊥.
Proof.
  rewrite and_def.
  rewrite not_false.
  rewrite true_or.
  now apply not_true.
Qed.

Theorem and_idem (p : t) : p ∧ p ≈ p.
Proof.
  rewrite and_def.
  rewrite or_idem.
  now apply not_not.
Qed.

Theorem and_comm (p q : t) : p ∧ q ≈ q ∧ p.
Proof.
  rewrite !and_def.
  now rewrite or_comm.
Qed.

Theorem and_assoc (p q r : t) : (p ∧ q) ∧ r ≈ p ∧ (q ∧ r).
Proof.
  rewrite !and_def.
  rewrite !not_not.
  now rewrite or_assoc.
Qed.

Theorem or_absorb (p q : t) : p ∨ (p ∧ q) ≈ p.
Proof.
  rewrite <- (huntington p q) at 1.
  rewrite and_def.
  rewrite <- (or_comm (¬(¬p ∨ ¬q))).
  rewrite <- or_assoc.
  rewrite or_idem.
  now apply huntington.
Qed.

Theorem and_absorb (p q : t) : p ∧ (p ∨ q) ≈ p.
Proof.
  rewrite and_def.
  rewrite <- (not_not p) at 2.
  rewrite <- (not_not q).
  rewrite <- (and_def (¬p)).
  rewrite or_absorb.
  now rewrite not_not.
Qed.

Theorem and_this_not_that (p q : t) : (p ∧ q) ∨ (p ∧ ¬q) ≈ p.
Proof.
  rewrite !and_def.
  rewrite not_not.
  now apply huntington.
Qed.

Theorem absurdity (p : t) : p ∧ ¬p ≈ ⊥.
Proof.
  rewrite and_def.
  now rewrite <- false_def.
Qed.

(** This proof was discovered by Don Monk. *)
Theorem and_or (p q r : t) : p ∧ (q ∨ r) ≈ (p ∧ q) ∨ (p ∧ r).
Proof.
  rewrite <- (and_this_not_that (p ∧ (q ∨ r)) q).
  rewrite !and_assoc.
  rewrite (and_comm _ q).
  rewrite and_absorb.
  rewrite <- (and_this_not_that (p ∧ q) r) at 1.
  rewrite <- (and_this_not_that (p ∧ (q ∨ r) ∧ ¬q) r).
  rewrite (and_assoc p ((q ∨ r) ∧ ¬q) r).
  rewrite (and_comm ((q ∨ r) ∧ ¬q) r).
  rewrite (or_comm q r) at 1.
  rewrite <- (and_assoc r (r ∨ q)).
  rewrite and_absorb.
  rewrite !and_assoc.
  rewrite <- not_or.
  rewrite absurdity.
  rewrite and_false.
  rewrite or_false.
  rewrite (and_comm r (¬q)).
  rewrite <- (or_idem (p ∧ q ∧ r)).
  rewrite !or_assoc.
  rewrite (or_comm (p ∧ q ∧ r)).
  rewrite !or_assoc.
  rewrite (or_comm _ (p ∧ q ∧ r)).
  rewrite <- or_assoc.
  rewrite <- and_assoc.
  rewrite <- and_assoc.
  rewrite and_this_not_that.
  rewrite and_assoc.
  rewrite !(and_comm _ r).
  rewrite <- and_assoc.
  rewrite <- and_assoc.
  rewrite and_this_not_that.
  now rewrite (and_comm _ r).
Qed.

Theorem and_or_r (p q r : t) : (q ∨ r) ∧ p ≈ (q ∧ p) ∨ (r ∧ p).
Proof.
  rewrite and_comm.
  rewrite and_or.
  rewrite !(and_comm p).
  reflexivity.
Qed.

Theorem or_and (p q r : t) : p ∨ (q ∧ r) ≈ (p ∨ q) ∧ (p ∨ r).
Proof.
  rewrite <- (not_not p) at 1.
  rewrite and_def.
  rewrite <- (not_not (¬¬p ∨ ¬(¬q ∨ ¬r))).
  rewrite <- and_def.
  rewrite and_or.
  rewrite <- !not_or.
  now rewrite <- and_def.
Qed.

Theorem or_and_r (p q r : t) : (q ∧ r) ∨ p ≈ (q ∨ p) ∧ (r ∨ p).
Proof.
  rewrite or_comm.
  rewrite or_and.
  rewrite !(or_comm p).
  reflexivity.
Qed.

Theorem or_not_absorb (p q : t) : p ∨ (¬p ∧ q) ≈ p ∨ q.
Proof.
  rewrite or_and.
  rewrite true_def.
  now rewrite true_and.
Qed.

Theorem and_not_absorb (p q : t) : p ∧ (¬p ∨ q) ≈ p ∧ q.
Proof.
  rewrite and_or.
  rewrite absurdity.
  now rewrite false_or.
Qed.

Theorem and_proj (p q : t) : p ∧ q ⟹ p.
Proof.
  apply impl_def.
  rewrite and_def.
  rewrite not_not.
  rewrite or_comm.
  rewrite <- or_assoc.
  rewrite true_def.
  now rewrite true_or.
Qed.

Theorem and_proj_r (p q : t) : q ∧ p ⟹ p.
Proof.
  rewrite and_comm.
  now apply and_proj.
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

Theorem and_impl (p q r : t) : p ∧ q ⇒ r ≈ p ⇒ (q ⇒ r).
Proof.
  rewrite and_def.
  rewrite not_not.
  now rewrite <- or_assoc.
Qed.

Theorem impl_and (p q r : t) : p ⇒ q ∧ r ≈ (p ⇒ q) ∧ (p ⇒ r).
Proof. now rewrite <- or_and. Qed.

Theorem or_impl (p q r : t) : p ∨ q ⇒ r ≈ (p ⇒ r) ∧ (q ⇒ r).
Proof.
  rewrite !(or_comm _ r).
  rewrite <- or_and.
  rewrite and_def.
  now rewrite !not_not.
Qed.

Theorem and_apply (p q : t) : p ∧ (p ⇒ q) ≈ p ∧ q.
Proof. now rewrite and_or; boolean. Qed.

Theorem and_impl_iff (p q r : t) : (p ∧ q ⟹ r) <-> (p ⟹ (q ⇒ r)).
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

Theorem impl_trans (p q r : t) : (p ⇒ q) ∧ (q ⇒ r) ⟹ (p ⇒ r).
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

Theorem impl_apply (p q : t) : (p ⇒ q) ∧ p ≈ p ∧ q.
Proof. now boolean. Qed.

Theorem or_impl_iff (p q r : t) : (p ∨ q ⟹ r) <-> (p ⇒ r) ∧ (q ⇒ r) ≈ ⊤.
Proof.
  split; intros.
  - rewrite !(or_comm _ r).
    rewrite <- or_and.
    rewrite and_def.
    rewrite !not_not.
    split.
    + now apply impl_true.
    + rewrite <- H at 1.
      now rewrite true_def.
  - rewrite !(or_comm _ r) in H.
    rewrite <- or_and in H.
    rewrite and_def in H.
    rewrite !not_not in H.
    rewrite or_comm in H.
    apply impl_def.
    now rewrite H.
Qed.

Theorem impl_iff (p q : t) : (p ⟹ q) <-> (p ⇒ q ≈ ⊤).
Proof.
  split; intro.
  - apply true_impl.
    rewrite <- H.
    now boolean.
  - apply impl_def.
    now rewrite <- H.
Qed.

Theorem or_excl_middle (p q : t) : p ∨ q ≈ p ∨ (¬ p ∧ q).
Proof.
  rewrite or_and.
  now boolean.
Qed.

Theorem or_monotonicity (p q r : t) : (p ⇒ q) ⟹ (p ∨ r ⇒ q ∨ r).
Proof.
  rewrite not_or.
  rewrite <- or_assoc.
  rewrite !or_and_r.
  rewrite !(or_comm _ r).
  rewrite <- !or_assoc.
  boolean.
  rewrite (or_comm r).
  now rewrite <- (or_inj _ r).
Qed.

Theorem or_and_or (p q r s : t) :
  (p ∨ q) ∧ (r ∨ s) ≈ (p ∧ r) ∨ (p ∧ s) ∨ (r ∧ q) ∨ (s ∧ q).
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

Theorem and_or_and (p q r s : t) :
  (p ∧ q) ∨ (r ∧ s) ≈ (p ∨ r) ∧ (p ∨ s) ∧ (r ∨ q) ∧ (s ∨ q).
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

Lemma or_respects  (p q r s : t) : (p ⇒ r) ∧ (q ⇒ s) ⟹ (p ∨ q ⇒ r ∨ s).
Proof.
  rewrite or_impl.
  rewrite <- (or_inj r) at 1.
  rewrite (or_comm r s).
  rewrite <- (or_inj s).
  reflexivity.
Qed.

Lemma and_respects  (p q r s : t) : (p ⇒ r) ∧ (q ⇒ s) ⟹ (p ∧ q ⇒ r ∧ s).
Proof.
  rewrite or_and_or.
  rewrite (and_def p q).
  rewrite not_not.
  rewrite <- !or_assoc.
  rewrite (and_comm r s).
  apply or_respects_impl; [|reflexivity].
  rewrite <- and_or.
  now rewrite !and_proj.
Qed.

End BooleanLogicFacts.
