Set Warnings "-local-declaration".

Require Import
  Coq.Unicode.Utf8
  Coq.Program.Program
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid
  Bool.

(***********************************************************************
 * This axiomatization of Linear Temporal Logic follows directly from
 * the paper:
 *
 * "A Calculational Deductive System for Linear Temporal Logic"
 * https://dl.acm.org/doi/10.1145/3387109
 *
 * by Warford, Vega and Staley *)

Module Type MinimalLinearTemporalLogic <: BooleanLogic.

Include BooleanLogic.

Parameter next  : t -> t.
Parameter until : t -> t -> t.

#[global]
Declare Scope ltl_scope.
Bind Scope ltl_scope with t.
Delimit Scope ltl_scope with ltl.
Open Scope boolean_scope.
Open Scope ltl_scope.

Notation "◯ p"     := (next p)    (at level 75, right associativity) : ltl_scope.
Notation "p 'U' q" := (until p q) (at level 79, right associativity) : ltl_scope.

#[global]
Declare Instance next_respects_implies  : Proper (implies ==> implies) next.
#[global]
Declare Instance until_respects_implies : Proper (implies ==> implies ==> implies) until.

Axiom (* 1 *)   next_not   : ∀ p,   ◯ ¬p ≈ ¬◯ p.
Axiom (* 2 *)   next_impl  : ∀ p q, ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Axiom (* 9 *)   next_until : ∀ p q, ◯ (p U q) ≈ ◯ p U ◯ q.

Axiom (* 10 *)  until_expand  : ∀ p q, p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Axiom (* 11 *)  until_false   : ∀ p,   p U ⊥ ⟹ ⊥.
Axiom (* NEW *) looped        : ∀ p,   ◯ ¬p U p ⟹ p.

Axiom (* 12 *)  until_left_or  : ∀ p q r, p U (q ∨ r) ≈  (p U q) ∨ (p U r).
Axiom (* 14 *)  until_left_and : ∀ p q r, p U (q ∧ r) ⟹ (p U q) ∧ (p U r).

Axiom (* NEW *) until_and_until : ∀ p q r s,
  (p U q) ∧ (r U s) ⟹ (p ∧ r) U ((q ∧ r) ∨ (p ∧ s) ∨ (q ∧ s)).

Axiom (* 17 *)  until_left_or_order   : ∀ p q r, p U (q U r) ⟹ (p ∨ q) U r.
Axiom (* 18 *)  until_right_and_order : ∀ p q r, p U (q ∧ r) ⟹ (p U q) U r.

Axiom (* 170 *) not_until : ∀ p q, ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).

End MinimalLinearTemporalLogic.

Module MinimalLinearTemporalLogicFacts (Import L : MinimalLinearTemporalLogic).

Module Import BF  := BooleanLogicFacts L.
Module Import MBF := BF.MBF.

#[local] Obligation Tactic := solve [ one_arg | two_arg ].

#[global]
Program Instance next_respects_equivalent :
  Proper (equivalent ==> equivalent) next.
#[global]
Program Instance until_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) until.

(*** 3.1 Next ◯ *)

(**
(1) Axiom, Self-dual : ◯ ¬p ≡ ¬◯ p
(2) Axiom, Distributivity of ◯ over ⟹ : ◯ (p ⇒ q) ≡ ◯ p ⇒ ◯ q
(3) Linearity : ◯ p ≡ ¬◯ ¬p
(4) Distributivity of ◯ over ∨ : ◯ (p ∨ q) ≡ ◯ p ∨ ◯ q
(5) Distributivity of ◯ over ∧ : ◯ (p ∧ q) ≡ ◯ p ∧ ◯ q
(6) Distributivity of ◯ over ≡ : ◯ (p ≡ q) ≡ ◯ p ≡ ◯ q
(7) Truth of ◯ : ◯ true ≡ true
(8) Falsehood of ◯ : ◯ false ≡ false
*)

Theorem (* 3 *) next_linearity p : ◯ p ≈ ¬◯ ¬p.
Proof.
  rewrite next_not.
  now rewrite not_not.
Qed.

Theorem (* 4 *) next_or p q : ◯ (p ∨ q) ≈ ◯ p ∨ ◯ q.
Proof.
  pose proof (next_impl (¬p) q) as H.
  rewrite not_not in H.
  rewrite H.
  now rewrite <- next_linearity.
Qed.

Theorem (* 5 *) next_and p q : ◯ (p ∧ q) ≈ ◯ p ∧ ◯ q.
Proof.
  rewrite <- (not_not p) at 1.
  rewrite <- (not_not q) at 1.
  rewrite <- not_or.
  rewrite next_not.
  rewrite next_or.
  rewrite not_or.
  now rewrite <- !next_linearity.
Qed.

Theorem (* 6 *) next_eqv p q : ◯ (p ≡ q) ≈ ◯ p ≡ ◯ q.
Proof.
  rewrite <- !next_not.
  rewrite <- !next_or.
  rewrite !and_def.
  rewrite <- !next_not.
  rewrite <- !next_or.
  now rewrite <- !next_not.
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

Corollary (* NEW *) until_expand_ext p q : p U q ≈ q ∨ (¬ q ∧ p ∧ ◯ (p U q)).
Proof.
  rewrite or_and.
  boolean.
  now apply until_expand.
Qed.

(*** 3.2 Until U *)

(**
(9) Axiom, Distributivity of ◯ over U : ◯ (p U q) ≡ p U ◯ q
(10) Axiom, Expand of U : p U q ≡ q ∨ (p ∧ ◯ (p U q))
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

Theorem (* NEW *) and_until_and p q r s : (p ∧ r) U (q ∧ s) ⟹ (p U q) ∧ (r U s).
Proof.
  rewrite until_left_and.
  rewrite (and_proj p) at 1.
  rewrite (and_proj_r r) at 1.
  reflexivity.
Qed.

Theorem (* NEW *) and_until_or p q r s : (p ∧ r) U (q ∨ s) ⟹ (p U q) ∨ (r U s).
Proof.
  rewrite <- (and_proj p r) at 2.
  rewrite <- (and_proj r p) at 3.
  rewrite (and_comm r p).
  rewrite <- until_left_or.
  reflexivity.
Qed.

Theorem (* NEW *) until_or_until_ext p q r s :
  (p ∧ r) U ((q ∨ r) ∧ (p ∨ s) ∧ (q ∨ s)) ⟹ (p U q) ∨ (r U s).
Proof.
  rewrite <- (and_proj p r) at 3.
  rewrite <- (and_proj r p) at 4.
  rewrite (and_comm r p).
  rewrite <- until_left_or.
  rewrite (and_proj_r (_ ∨ _)).
  rewrite (and_proj_r (_ ∨ _)).
  reflexivity.
Qed.

Theorem (* 13 *) until_right_or p q r : (p U r) ∨ (q U r) ⟹ (p ∨ q) U r.
Proof.
  rewrite (or_inj p q) at 1.
  rewrite (or_inj q p) at 2.
  rewrite (or_comm q p).
  rewrite (* 12 *) <- until_left_or.
  now rewrite or_idem.
Qed.

Theorem (* 12 *) until_left_or_alt p q r : p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Proof.
  split.
  - rewrite <- and_until_or.
    now rewrite and_idem.
  - rewrite (or_inj q r) at 1.
    rewrite (or_inj_r r q) at 2.
    now rewrite or_idem.
Qed.

Theorem (* NEW *) until_and_right_or p q r : (p U r) ∧ (q U r) ⟹ p U (q ∨ r).
Proof.
  rewrite and_proj.
  now rewrite <- or_inj_r.
Qed.

Theorem (* NEW *) until_and_left_or p q r : (p U r) ∧ (q U r) ⟹ (p ∨ q) U r.
Proof.
  rewrite and_proj.
  now rewrite <- or_inj.
Qed.

Theorem (* NEW *) until_and_or_right p q r : (p U q) ∧ (p U r) ⟹ p U (q ∨ r).
Proof.
  rewrite and_proj.
  now rewrite <- or_inj.
Qed.

Theorem (* NEW *) until_and_or_left p q r : (p U q) ∧ (p U r) ⟹ (p ∨ q) U r.
Proof.
  rewrite and_proj_r.
  now rewrite <- or_inj.
Qed.

Theorem (* 15 *) until_right_and p q r : (p ∧ q) U r ≈ (p U r) ∧ (q U r).
Proof.
  split.
  - rewrite <- (and_idem r) at 1.
    rewrite (* 14 *) until_left_and.
    rewrite (and_proj p) at 1.
    now rewrite (and_proj_r q).
  - rewrite (* NEW *) until_and_until.
    boolean.
    rewrite (and_proj r).
    rewrite (and_proj_r r).
    now boolean.
Qed.

Theorem (* NEW *) until_and_until_ext p q r s : (p U q) ∧ (r U s) ⟹ (p ∧ r) U (q ∨ s).
Proof.
  rewrite until_right_and.
  rewrite <- (or_inj q) at 1.
  rewrite <- (or_inj_r s).
  reflexivity.
Qed.

Theorem (* NEW *) until_or_right_and p q r : p U (q ∧ r) ⟹ (p U r) ∨ (q U r).
Proof.
  rewrite and_proj_r.
  now rewrite <- or_inj.
Qed.

Theorem (* NEW *) until_or_left_and p q r : (p ∧ q) U r ⟹ (p U r) ∨ (q U r).
Proof.
  rewrite and_proj_r.
  now rewrite <- or_inj_r.
Qed.

Theorem (* NEW *) until_or_and_right p q r : p U (q ∧ r) ⟹ (p U q) ∨ (p U r).
Proof.
  rewrite and_proj_r.
  now rewrite <- or_inj_r.
Qed.

Theorem (* NEW *) until_or_and_left p q r : (p ∧ q) U r ⟹ (p U q) ∨ (p U r).
Proof.
  rewrite and_proj.
  now rewrite <- or_inj_r.
Qed.

Theorem (* 16 *) until_impl_order p q r : (p U q) ∧ (¬q U r) ⟹ p U r.
Proof.
  rewrite (* NEW *) until_and_until.
  boolean.
  rewrite <- and_or_r.
  rewrite (* 14 *) until_left_and.
  rewrite and_proj_r.
  now rewrite and_proj.
Qed.

Theorem (* 19 *) until_right_impl p q r : (p ⇒ q) U r ⟹ (p U r) ⇒ (q U r).
Proof.
  apply and_impl_iff.
  rewrite <- until_right_and.
  rewrite and_comm.
  rewrite and_apply.
  rewrite until_right_and.
  rewrite and_comm.
  now apply and_proj.
Qed.

Theorem (* 20 *) until_true p : p U ⊤ ≈ ⊤.
Proof.
  rewrite until_expand.
  now rewrite true_or.
Qed.

Theorem (* 21 *) false_until p : ⊥ U p ≈ p.
Proof.
  rewrite until_expand.
  rewrite false_and.
  now rewrite or_false.
Qed.

Theorem (* 22 *) until_idem p : p U p ≈ p.
Proof.
  rewrite until_expand.
  now rewrite or_absorb.
Qed.

Theorem (* 23 *) until_excl_middle p q : (p U q) ∨ (p U ¬q) ≈ ⊤.
Proof.
  rewrite <- until_left_or.
  rewrite true_def.
  now apply until_true.
Qed.

Theorem (* 24 *) until_24 p q r : (¬p U (q U r)) ∧ (p U r) ⟹ q U r.
Proof.
  rewrite until_left_or_order.
  rewrite until_right_impl.
  rewrite and_comm.
  rewrite and_or.
  now boolean.
Qed.

Theorem (* 25 *) until_25 p q r : (p U (¬q U r)) ∧ (q U r) ⟹ p U r.
Proof.
  rewrite until_left_or_order.
  rewrite or_comm.
  rewrite until_right_impl.
  rewrite and_comm.
  rewrite and_or.
  now boolean.
Qed.

Theorem (* 26 *) until_26 p q : (p U q) ∧ (¬q U p) ⟹ p.
Proof.
  rewrite until_impl_order.
  now rewrite until_idem.
Qed.

Theorem (* 27 *) until_27 p q : p ∧ (¬p U q) ⟹ q.
Proof.
  rewrite until_expand.
  rewrite and_or.
  rewrite <- and_assoc.
  now boolean.
Qed.

Theorem (* 28 *) until_28 p q : p U q ⟹ p ∨ q.
Proof.
  rewrite until_expand.
  rewrite or_and.
  rewrite and_proj.
  now rewrite or_comm.
Qed.

Theorem (* 29 *) until_insertion p q : q ⟹ p U q.
Proof.
  rewrite until_expand.
  now apply or_inj.
Qed.

Theorem (* 30 *) until_30 p q : p ∧ q ⟹ p U q.
Proof.
  rewrite until_expand.
  rewrite <- or_inj.
  rewrite and_comm.
  now apply and_proj.
Qed.

Theorem (* 31 *) until_absorb_or_u p q : p ∨ (p U q) ≈ p ∨ q.
Proof.
  split.
  - rewrite (until_28 p q) at 1.
    rewrite <- or_assoc.
    now rewrite or_idem.
  - now rewrite <- until_insertion.
Qed.

Theorem (* 32 *) until_absorb_u_or p q : (p U q) ∨ q ≈ p U q.
Proof.
  rewrite until_expand.
  rewrite or_comm at 1.
  rewrite <- or_assoc.
  now rewrite or_idem.
Qed.

Theorem (* 33 *) until_absorb_u_and p q : (p U q) ∧ q ≈ q.
Proof.
  split.
  - rewrite and_comm.
    now apply and_proj.
  - rewrite <- and_idem at 1.
    now rewrite (until_insertion p q) at 1.
Qed.

Theorem (* 34 *) until_absorb_u_or_and p q : (p U q) ∨ (p ∧ q) ≈ p U q.
Proof.
  split.
  - rewrite until_30.
    now rewrite or_idem.
  - now rewrite <- or_inj.
Qed.

Theorem (* 35 *) until_absorb_u_and_or p q : (p U q) ∧ (p ∨ q) ≈ p U q.
Proof.
  split.
  - now apply and_proj.
  - rewrite <- until_28.
    now rewrite and_idem.
Qed.

Theorem (* 36 *) until_left_absorb p q : p U (p U q) ≈ p U q.
Proof.
  split.
  - rewrite until_left_or_order.
    now rewrite or_idem.
  - now apply until_insertion.
Qed.

Theorem (* 37 *) until_right_absorb p q : (p U q) U q ≈ p U q.
Proof.
  split.
  - rewrite until_28.
    now apply until_absorb_u_or.
  - rewrite <- until_right_and_order.
    now rewrite and_idem.
Qed.

Corollary (* NEW *) until_impl p q r : (p ⇒ r) ∧ (q ⇒ r) ⟹ (p U q ⇒ r).
Proof.
  rewrite or_respects.
  rewrite until_28.
  now rewrite or_idem.
Qed.

End MinimalLinearTemporalLogicFacts.
