Set Warnings "-local-declaration".

Require Import
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

Parameters s : Type.

Parameter holds : s -> nat -> t -> Prop.

Parameter next : t -> t.
Parameter until : t -> t -> t.

Declare Scope ltl_scope.
Bind Scope ltl_scope with t.
Delimit Scope ltl_scope with ltl.
Open Scope boolean_scope.
Open Scope ltl_scope.

Notation "[ σ , j ]  ⊨ p" := (holds σ j p) (at level 89, no associativity) : ltl_scope.
Notation "◯ p"            := (next p)      (at level 75, right associativity) : ltl_scope.
Notation "p 'U' q"        := (until p q)   (at level 79, right associativity) : ltl_scope.

Definition t_implies    p q := forall σ j, holds σ j (impl p q).
Definition t_equivalent p q := t_implies p q /\ t_implies q p.

Declare Instance holds_respects_implies σ j :
  Proper (implies ==> Basics.impl) (holds σ j).
Declare Instance holds_respects_temporality σ j :
  Proper ((fun p q => holds σ j (impl p q)) ==> Basics.impl) (holds σ j).

Declare Instance next_respects_implies : Proper (implies ==> implies) next.
Declare Instance until_respects_implies : Proper (implies ==> implies ==> implies) until.

Infix "⟹" := t_implies    (at level 99, right associativity) : ltl_scope.
Infix "≈"  := t_equivalent (at level 90, no associativity) : ltl_scope.

Axiom truth_holds : forall p, truth p <-> forall σ j, holds σ j p.

Axiom next_semantics : forall σ j p, [σ, j] ⊨ ◯ p <-> [σ, j + 1] ⊨ p.

Axiom (* 1 *)  next_not : forall p, ◯ ¬p ≈ ¬◯ p.
Axiom (* 2 *)  next_impl : forall p q, ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.

Axiom (* 9 *)  next_until : forall p q, ◯ (p U q) ≈ (◯ p) U (◯ q).
Axiom (* 10 *) until_expansion : forall p q, p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Axiom (* 11 *) until_right_bottom : forall p, p U ⊥ ≈ ⊥.
Axiom (* 12 *) until_left_or : forall p q r, p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Axiom (* 13 *) until_right_or : forall p q r, (p U r) ∨ (q U r) ⟹ (p ∨ q) U r.
Axiom (* 14 *) until_left_and : forall p q r, p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Axiom (* 15 *) until_right_and : forall p q r, (p ∧ q) U r ≈ (p U r) ∧ (q U r).
Axiom (* 16 *) until_impl_order : forall p q r, (p U q) ∧ (¬q U r) ⟹ p U r.
Axiom (* 17 *) until_right_or_order : forall p q r, p U (q U r) ⟹ (p ∨ q) U r.
Axiom (* 18 *) until_right_and_order : forall p q r, p U (q ∧ r) ⟹ (p U q) U r.

(** jww (2021-02-08): This axiom is just an idea a work in progress *)
(* Axiom (* NEW *) until_continue : forall p q, q ∧ p U ◯ ¬q ⟹ p U (q ∧ ◯ ¬q). *)
Axiom (* NEW *) always_until : forall p q r, ¬(⊤ U ¬p) ∧ q U r ≈ (p ∧ q) U (p ∧ r).
Axiom (* NEW *) not_until    : forall p q, ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).

End MinimalLinearTemporalLogic.

Module MinimalLinearTemporalLogicFacts (L : MinimalLinearTemporalLogic).

Import L.
Module Import BF := BooleanLogicFacts L.
Module Import MBF := BF.MBF.

Lemma t_impl p q : (p ⟹ q)%boolean <-> (p ⟹ q).
Proof.
  unfold t_implies.
  split; intro H.
  - apply truth_holds.
    now apply H.
  - apply truth_holds in H.
    now apply H.
Qed.

Lemma t_eqv p q : (p ≈ q)%boolean <-> p ≈ q.
Proof.
  unfold t_equivalent.
  split; intro H.
  - destruct H.
    split; now apply t_impl.
  - destruct H.
    split; now apply t_impl.
Qed.

Program Instance next_respects_equivalent :
  Proper (equivalent ==> equivalent) next.
Program Instance until_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) until.

Local Obligation Tactic := program_simpl.

Program Instance t_implies_reflexive : Reflexive t_implies.
Next Obligation.
  unfold t_implies; intros.
  apply truth_holds.
  reflexivity.
Qed.

Program Instance t_implies_transitive : Transitive t_implies.
Next Obligation.
  unfold t_implies in *; intros.
  apply truth_holds in H.
  apply truth_holds in H0.
  apply truth_holds.
  now transitivity y.
Qed.

Program Instance t_equivalent_Equivalence : Equivalence t_equivalent.
Next Obligation. now intro x; split. Qed.
Next Obligation. repeat intro; split; destruct H; now intuition. Qed.
Next Obligation. repeat intro; split; destruct H, H0; now transitivity y. Qed.

Arguments holds_respects_temporality {_ _ _ _} H.

Program Instance holds_respects_t_implies σ j :
  Proper (t_implies ==> Basics.impl) (holds σ j).
Next Obligation.
  repeat intro.
  now apply (holds_respects_temporality (H σ j)).
Qed.

Program Instance holds_respects_equivalent σ j :
  Proper (equivalent ==> iff) (holds σ j).
Next Obligation.
  repeat intro.
  destruct H.
  split; intro.
  - unfold implies in H.
    pose proof (proj1 (truth_holds _) H).
    now apply (holds_respects_temporality (H2 σ j)).
  - unfold implies in H0.
    pose proof (proj1 (truth_holds _) H0).
    now apply (holds_respects_temporality (H2 σ j)).
Qed.

Program Instance holds_respects_t_equivalent σ j :
  Proper (t_equivalent ==> iff) (holds σ j).
Next Obligation.
  repeat intro.
  destruct H.
  split; intro.
  - now rewrite <- H.
  - now rewrite <- H0.
Qed.

Program Instance t_implies_respects_implies :
  Proper (implies --> implies ==> Basics.impl) t_implies.
Next Obligation.
  repeat intro.
  unfold Basics.flip in H.
  apply truth_holds in H1.
  revert j.
  revert σ.
  apply truth_holds.
  now rewrite H, <- H0.
Qed.

Program Instance t_implies_respects_t_implies :
  Proper (t_implies --> t_implies ==> Basics.impl) t_implies.
Next Obligation.
  repeat intro.
  unfold Basics.flip in H.
  apply truth_holds in H.
  apply truth_holds in H0.
  apply truth_holds in H1.
  revert j.
  revert σ.
  apply truth_holds.
  now rewrite H, <- H0.
Qed.

Program Instance t_implies_respects_equivalent :
  Proper (equivalent ==> equivalent ==> iff) t_implies.
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros.
  - now rewrite H1, H3, H0.
  - now rewrite <- H2, <- H3, <- H.
Qed.

Program Instance t_implies_respects_t_equivalent :
  Proper (t_equivalent ==> t_equivalent ==> iff) t_implies.
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros.
  - now rewrite H1, H3, H0.
  - now rewrite <- H2, <- H3, <- H.
Qed.

Program Instance t_equivalent_respects_equivalent :
  Proper (equivalent ==> equivalent ==> iff) t_equivalent.
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros.
  - split; intros.
    + destruct H3.
      now rewrite H1, H3, H0.
    + destruct H3.
      now rewrite H2, H4, H.
  - split; intros.
    + destruct H3.
      now rewrite H, H3, H2.
    + destruct H3.
      now rewrite H0, H4, H1.
Qed.

Program Instance t_equivalent_respects_t_equivalent :
  Proper (t_equivalent ==> t_equivalent ==> iff) t_equivalent.
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros.
  - split; intros.
    + destruct H3.
      now rewrite H1, H3, H0.
    + destruct H3.
      now rewrite H2, H4, H.
  - split; intros.
    + destruct H3.
      now rewrite H, H3, H2.
    + destruct H3.
      now rewrite H0, H4, H1.
Qed.

Program Instance impl_respects_t_implies :
  Proper (t_implies --> t_implies ==> t_implies) impl.
Next Obligation.
  repeat intro.
  apply truth_holds in H.
  apply truth_holds in H0.
  apply truth_holds.
  rewrite <- H.
  rewrite H0.
  reflexivity.
Qed.

Program Instance impl_respects_t_equivalent :
  Proper (t_equivalent ==> t_equivalent ==> t_equivalent) impl.
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros.
  + now rewrite <- H1, H0.
  + now rewrite <- H, H2.
Qed.

Program Instance not_respects_t_implies : Proper (t_implies --> t_implies) not.
Next Obligation.
  repeat intro.
  unfold flip in H.
  apply truth_holds in H.
  apply truth_holds.
  now rewrite H.
Qed.

Program Instance not_respects_t_equivalent :
  Proper (t_equivalent ==> t_equivalent) not.
Next Obligation.
  repeat intro.
  destruct H.
  split; intros.
  - now rewrite H0.
  - now rewrite H.
Qed.

Program Instance or_respects_t_implies :
  Proper (t_implies ==> t_implies ==> t_implies) or.
Next Obligation.
  repeat intro.
  apply truth_holds in H.
  apply truth_holds in H0.
  apply truth_holds.
  now rewrite H, H0.
Qed.

Program Instance or_respects_t_equivalent :
  Proper (t_equivalent ==> t_equivalent ==> t_equivalent) or.
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros.
  - now rewrite H, H0.
  - now rewrite H1, H2.
Qed.

Program Instance and_respects_t_implies :
  Proper (t_implies ==> t_implies ==> t_implies) and.
Next Obligation.
  repeat intro.
  apply truth_holds in H.
  apply truth_holds in H0.
  apply truth_holds.
  now rewrite H, H0.
Qed.

Program Instance and_respects_t_equivalent :
  Proper (t_equivalent ==> t_equivalent ==> t_equivalent) and.
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros.
  - now rewrite H, H0.
  - now rewrite H1, H2.
Qed.

Program Instance next_respects_t_implies :
  Proper (t_implies ==> t_implies) next.
Next Obligation.
  repeat intro.
  rewrite <- next_impl.
  rewrite next_semantics.
  now apply H.
Qed.

Program Instance next_respects_t_equivalent :
  Proper (t_equivalent ==> t_equivalent) next.
Next Obligation.
  repeat intro.
  destruct H.
  split; intros.
  - now rewrite <- H.
  - now rewrite <- H0.
Qed.

Program Instance until_respects_t_implies :
  Proper (t_implies ==> t_implies ==> t_implies) until.

Program Instance until_respects_t_equivalent :
  Proper (t_equivalent ==> t_equivalent ==> t_equivalent) until.

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

Theorem (* 3 *) next_linearity p : ◯ p ≈ ¬◯ ¬p.
Proof.
  rewrite next_not.
  now rewrite not_not.
Qed.

Theorem (* 4 *) next_or p q : ◯ (p ∨ q) ≈ ◯ p ∨ ◯ q.
Proof.
  pose proof (next_impl (¬p) q) as H.
  rewrite !impl_def in H.
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

Notation "p ≡ q" := (¬(¬(p ⇒ q) ∨ ¬(p ⇒ q))) (at level 86, right associativity) : boolean_scope.

Theorem (* 6 *) next_eqv p q : ◯ (p ≡ q) ≈ ◯ p ≡ ◯ q.
Proof.
  rewrite !impl_def.
  rewrite <- !next_not.
  rewrite <- !next_or.
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
  rewrite until_expansion.
  now rewrite true_or.
Qed.

Theorem (* 21 *) false_until p : ⊥ U p ≈ p.
Proof.
  rewrite until_expansion.
  rewrite false_and.
  now rewrite or_false.
Qed.

Theorem (* 22 *) until_idem p : p U p ≈ p.
Proof.
  rewrite until_expansion.
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
  rewrite until_right_or_order.
  rewrite until_right_impl.
  rewrite and_comm.
  rewrite and_or.
  now boolean.
Qed.

Theorem (* 25 *) until_25 p q r : (p U (¬q U r)) ∧ (q U r) ⟹ p U r.
Proof.
  rewrite until_right_or_order.
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
  rewrite until_expansion.
  rewrite and_or.
  rewrite <- and_assoc.
  now boolean.
Qed.

Theorem (* 28 *) until_28 p q : p U q ⟹ p ∨ q.
Proof.
  rewrite until_expansion.
  rewrite or_and.
  rewrite and_proj.
  now rewrite or_comm.
Qed.

Theorem (* 29 *) until_insertion p q : q ⟹ p U q.
Proof.
  rewrite until_expansion.
  now apply or_inj.
Qed.

Theorem (* 30 *) until_30 p q : p ∧ q ⟹ p U q.
Proof.
  rewrite until_expansion.
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
  rewrite until_expansion.
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
  - rewrite until_right_or_order.
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

Theorem (* NEW *) until_left_and_impl p q r : p U q ∧ p U r ⟹ p U (q ∨ r).
Proof.
  rewrite until_left_or.
  rewrite and_proj.
  rewrite <- or_inj.
  reflexivity.
Qed.

End MinimalLinearTemporalLogicFacts.
