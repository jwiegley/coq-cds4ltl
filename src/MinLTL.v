Set Warnings "-local-declaration".

Require Import
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.SetoidClass
  Bool.

(***********************************************************************
 * This axiomatization of Linear Temporal Logic follows directly from
 * the paper:
 *
 * "A Calculational Deductive System for Linear Temporal Logic"
 * https://dl.acm.org/doi/10.1145/3387109
 *
 * by Warford, Vega and Staley *)

Module Type MinimalLinearTemporalLogic.

Declare Module Bool : BooleanLogic.
Include Bool.

Parameter next : t -> t.
Parameter until : t -> t -> t.

Notation "◯ p"     := (next p)    (at level 0, right associativity).
Notation "p 'U' q" := (until p q) (at level 44, right associativity).

Declare Instance next_respects_impl : Proper (impl ==> impl) next.
Program Instance next_respects_eqv : Proper (eqv ==> eqv) next.
Declare Instance until_respects_impl : Proper (impl ==> impl ==> impl) until.
Program Instance until_respects_eqv : Proper (eqv ==> eqv ==> eqv) until.

(*** 3.1 Next ◯ *)

(**
(1) Axiom, Self-dual : ◯ ¬p ≡ ¬◯ p
(2) Axiom, Distributivity of ◯ over ⟹ : ◯ (p ⇒ q) ≡ ◯ p ⇒ ◯ q
(3) Linearity : ◯ p ≡ ¬◯ ¬p
(4) Distributivity of ◯ over ∨ : ◯ (p ∨ q) ◯ ≡ p ∨ ◯ q
(5) Distributivity of ◯ over ∧ : ◯ (p ∧ q) ◯ ≡ p ∧ ◯ q
(6) Distributivity of ◯ over ≡ : ◯ (p ≡ q) ≡ ◯ p ≡ ◯ q
(7) Truth of ◯ : ◯ true ≡ true
(8) Falsehood of ◯ : ◯ false ≡ false
*)

Axiom (* 1 *) next_not : forall (φ : t), ◯ ¬φ ≈ ¬◯ φ.
Axiom (* 2 *) next_impl : forall (φ ψ : t), ◯ (φ → ψ) ≈ ◯ φ → ◯ ψ.

Theorem (* 3 *) next_linearity (φ : t) : ◯ φ ≈ ¬◯ ¬φ.
Proof.
  rewrite next_not.
  now apply not_swap.
Qed.

Theorem (* 4 *) next_or (φ ψ : t) : ◯ (φ ∨ ψ) ≈ ◯ φ ∨ ◯ ψ.
Proof.
  pose proof (next_impl (¬φ) ψ) as H; rewrite not_not in H.
  rewrite H.
  now rewrite <- next_linearity.
Qed.

Theorem (* 5 *) next_and (φ ψ : t) : ◯ (φ ∧ ψ) ≈ ◯ φ ∧ ◯ ψ.
Proof.
  rewrite <- (not_not φ) at 1.
  rewrite <- (not_not ψ) at 1.
  rewrite <- not_or.
  rewrite next_not.
  rewrite next_or.
  rewrite not_or.
  now rewrite <- !next_linearity.
Qed.

Theorem (* 6 *) next_eqv (φ ψ : t) : ◯ (φ ≡ ψ) ≈ ◯ φ ≡ ◯ ψ.
Proof.
  rewrite !next_or.
  rewrite !next_not.
  now rewrite next_and.
Qed.

Theorem (* 7 *) next_true : ◯ ⊤ ≈ ⊤.
Proof.
  rewrite <- (true_def ⊤) at 1.
  rewrite next_or.
  rewrite next_not.
  now rewrite true_def.
Qed.

Theorem (* 8 *) next_false : ◯ ⊥ ≈ ⊥.
Proof.
  rewrite <- (false_def ⊥) at 1.
  rewrite next_not.
  rewrite next_or.
  rewrite next_not.
  now rewrite false_def.
Qed.

(*** 3.2 Until U *)

(**
(9) Axiom, Distributivity of ◯ over U : ◯ (p U q) ≡ p U ◯ q
(10) Axiom, Expansion of U : p U q ≡ q ∨ (p ∧ ◯ (p U q))
(11) Axiom, Right zero of U : p U false ≡ false
(12) Axiom, Left distributivity of U over ∨ : p U (q ∨ r) ≡ p U q ∨ p U r
(13) Axiom, Right distributivity of U over ∨ : p U r ∨ q U r ⇒ (p ∨ q) U r
(14) Axiom, Left distributivity of U over ∧ : p U (q ∧ r) ⇒ p U q ∧ p U r
(15) Axiom, Right distributivity of U over ∧ : (p ∧ q) U r ≡ p U r ∧ q U r
(16) Axiom, U implication ordering: p U q ∧ ¬q U r ⇒ p U r
(17) Axiom, Right U ∨ ordering: p U (q U r) ⇒ (p ∨ q) U r
(18) Axiom, Right ∧ U ordering: p U (q ∧ r) ⇒ (p U q) U r
(19) Right distributivity of U over ⇒ : (p ⇒ q) U r ⇒ (p U r ⇒ q U r)
(20) Right zero of U : p U true ≡ true
(21) Left identity of U : false U q ≡ q
(22) Idempotency of U : p U p ≡ p
(23) U excluded middle : p U q ∨ p U ¬q
(24) ¬p U (q U r) ∧ p U r ⇒ q U r
(25) p U (¬q U r) ∧ q U r ⇒ p U r
(26) p U q ∧ ¬q U p ⇒ p
(27) p ∧ ¬p U q ⇒ q
(28) p U q ⇒ p ∨ q
(29) U insertion: q ⇒ p U q
(30) p ∧ q ⇒ p U q
(31) Absorption : p ∨ p U q ≡ p ∨ q
(32) Absorption : p U q ∨ q ≡ p U q
(33) Absorption : p U q ∧ q ≡ q
(34) Absorption : p U q ∨ (p ∧ q) ≡ p U q
(35) Absorption : p U q ∧ (p ∨ q) ≡ p U q
(36) Left absorption of U : p U (p U q) ≡ p U q
(37) Right absorption of U : (p U q) U q ≡ p U q
*)

Axiom (* 9 *) next_until : forall (φ ψ : t), ◯ (φ U ψ) ≈ (◯ φ) U (◯ ψ).
Axiom (* 10 *) until_expansion : forall (φ ψ : t), φ U ψ ≈ ψ ∨ (φ ∧ ◯ (φ U ψ)).
Axiom (* 11 *) until_right_bottom : forall (φ : t), φ U ⊥ ≈ ⊥.
Axiom (* 12 *) until_left_or : forall (φ ψ χ : t), φ U (ψ ∨ χ) ≈ (φ U ψ) ∨ (φ U χ).
Axiom (* 13 *) until_right_or : forall (φ ψ χ : t), (φ U χ) ∨ (ψ U χ) ⟹ (φ ∨ ψ) U χ.
Axiom (* 14 *) until_left_and : forall (φ ψ χ : t), φ U (ψ ∧ χ) ⟹ (φ U ψ) ∧ (φ U χ).
Axiom (* 15 *) until_right_and : forall (φ ψ χ : t), (φ ∧ ψ) U χ ≈ (φ U χ) ∧ (ψ U χ).
Axiom (* 16 *) until_impl_order : forall (φ ψ χ : t), (φ U ψ) ∧ (¬ψ U χ) ⟹ φ U χ.
Axiom (* 17 *) until_right_or_order : forall (φ ψ χ : t), φ U (ψ U χ) ⟹ (φ ∨ ψ) U χ.
Axiom (* 18 *) until_right_and_order : forall (φ ψ χ : t), φ U (ψ ∧ χ) ⟹ (φ U ψ) U χ.

Theorem (* 19 *) until_right_impl (φ ψ χ : t) : (φ → ψ) U χ ⟹ (φ U χ) → (ψ U χ).
Proof.
  apply and_impl_iff.
  rewrite <- until_right_and.
  rewrite and_comm.
  rewrite and_apply.
  rewrite until_right_and.
  rewrite and_comm.
  now apply and_proj.
Qed.

Theorem (* 20 *) until_true (φ : t) : φ U ⊤ ≈ ⊤.
Proof.
  rewrite until_expansion.
  now rewrite true_or.
Qed.

Theorem (* 21 *) false_until (φ : t) : ⊥ U φ ≈ φ.
Proof.
  rewrite until_expansion.
  rewrite false_and.
  now rewrite or_false.
Qed.

Theorem (* 22 *) until_idem (φ : t) : φ U φ ≈ φ.
Proof.
  rewrite until_expansion.
  now rewrite or_absorb.
Qed.

Theorem (* 23 *) until_excl_middle (φ ψ : t) : (φ U ψ) ∨ (φ U ¬ψ) ≈ ⊤.
Proof.
  rewrite <- until_left_or.
  rewrite true_def.
  now apply until_true.
Qed.

Theorem (* 24 *) until_24 (φ ψ χ : t) : (¬φ U (ψ U χ)) ∧ (φ U χ) ⟹ ψ U χ.
Proof.
  rewrite until_right_or_order.
  rewrite until_right_impl.
  rewrite and_comm.
  rewrite and_or.
  now boolean.
Qed.

Theorem (* 25 *) until_25 (φ ψ χ : t) : (φ U (¬ψ U χ)) ∧ (ψ U χ) ⟹ φ U χ.
Proof.
  rewrite until_right_or_order.
  rewrite or_comm.
  rewrite until_right_impl.
  rewrite and_comm.
  rewrite and_or.
  now boolean.
Qed.

Theorem (* 26 *) until_26 (φ ψ : t) : (φ U ψ) ∧ (¬ψ U φ) ⟹ φ.
Proof.
  rewrite until_impl_order.
  now rewrite until_idem.
Qed.

Theorem (* 27 *) until_27 (φ ψ : t) : φ ∧ (¬φ U ψ) ⟹ ψ.
Proof.
  rewrite until_expansion.
  rewrite and_or.
  rewrite <- and_assoc.
  now boolean.
Qed.

Theorem (* 28 *) until_28 (φ ψ : t) : φ U ψ ⟹ φ ∨ ψ.
Proof.
  rewrite until_expansion.
  rewrite or_and.
  rewrite and_proj.
  now rewrite or_comm.
Qed.

Theorem (* 29 *) until_insertion (φ ψ : t) : ψ ⟹ φ U ψ.
Proof.
  rewrite until_expansion.
  now apply or_inj.
Qed.

Theorem (* 30 *) until_30 (φ ψ : t) : φ ∧ ψ ⟹ φ U ψ.
Proof.
  rewrite until_expansion.
  rewrite <- or_inj.
  rewrite and_comm.
  now apply and_proj.
Qed.

Theorem (* 31 *) until_absorb_or_u (φ ψ : t) : φ ∨ (φ U ψ) ≈ φ ∨ ψ.
Proof.
  split.
  - rewrite (until_28 φ ψ) at 1.
    rewrite <- or_assoc.
    now rewrite or_idem.
  - now rewrite <- until_insertion.
Qed.

Theorem (* 32 *) until_absorb_u_or (φ ψ : t) : (φ U ψ) ∨ ψ ≈ φ U ψ.
Proof.
  rewrite until_expansion.
  rewrite or_comm at 1.
  rewrite <- or_assoc.
  now rewrite or_idem.
Qed.

Theorem (* 33 *) until_absorb_u_and (φ ψ : t) : (φ U ψ) ∧ ψ ≈ ψ.
Proof.
  split.
  - rewrite and_comm.
    now apply and_proj.
  - rewrite <- and_idem at 1.
    now rewrite (until_insertion φ ψ) at 1.
Qed.

Theorem (* 34 *) until_absorb_u_or_and (φ ψ : t) : (φ U ψ) ∨ (φ ∧ ψ) ≈ φ U ψ.
Proof.
  split.
  - rewrite until_30.
    now rewrite or_idem.
  - now rewrite <- or_inj.
Qed.

Theorem (* 35 *) until_absorb_u_and_or (φ ψ : t) : (φ U ψ) ∧ (φ ∨ ψ) ≈ φ U ψ.
Proof.
  split.
  - now apply and_proj.
  - rewrite <- until_28.
    now rewrite and_idem.
Qed.

Theorem (* 36 *) until_left_absorb (φ ψ : t) : φ U (φ U ψ) ≈ φ U ψ.
Proof.
  split.
  - rewrite until_right_or_order.
    now rewrite or_idem.
  - now apply until_insertion.
Qed.

Theorem (* 37 *) until_right_absorb (φ ψ : t) : (φ U ψ) U ψ ≈ φ U ψ.
Proof.
  split.
  - rewrite until_28.
    now apply until_absorb_u_or.
  - rewrite <- until_right_and_order.
    now rewrite and_idem.
Qed.

Theorem (* NEW *) until_left_and_impl (φ ψ χ : t) : φ U ψ ∧ φ U χ ⟹ φ U (ψ ∨ χ).
Proof.
  rewrite until_left_or.
  rewrite and_proj.
  rewrite <- or_inj.
  reflexivity.
Qed.

Axiom (* NEW *) not_until : forall (φ ψ : t), ⊤ U ¬φ ∧ ¬(φ U ψ) ≈ ¬ψ U (¬φ ∧ ¬ψ).

End MinimalLinearTemporalLogic.
