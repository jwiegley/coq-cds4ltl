Set Warnings "-local-declaration".

Require Import
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid.

(***********************************************************************
 * This is a minimal Boolean Logic comprised of ∨, ¬ and three axioms. *)

Module Type MinimalBooleanLogic.

Parameter t : Type.             (* The type of boolean propositions *)

Parameter truth : t -> Prop.

(** The following three parameters are fundamental to this development. *)
Parameter not : t -> t.
Parameter or : t -> t -> t.

(** The next three parameters are syntactic terms whose defined may be
    expressed in terms of the fundamentals above. They are allowed here as
    parameters so module authors may chose more economical definitions. *)
Parameter impl : t -> t -> t.
Parameter eqv : t -> t -> t.
Parameter true : t.
Parameter false : t.

Declare Scope boolean_scope.
Bind Scope boolean_scope with t.
Delimit Scope boolean_scope with boolean.
Open Scope boolean_scope.

Notation "¬ p"    := (not p)    (at level 75, right associativity) : boolean_scope.
Infix    "∨"      := or         (at level 85, right associativity) : boolean_scope.
Infix    "⇒"      := impl       (at level 86, right associativity) : boolean_scope.
Infix    "≡"      := eqv        (at level 86, right associativity) : boolean_scope.
Notation "⊤"      := true       (at level 0, no associativity) : boolean_scope.
Notation "⊥"      := false      (at level 0, no associativity) : boolean_scope.

Definition implies    (x y : t) : Prop := truth (impl x y).
Definition equivalent (x y : t) : Prop := implies x y /\ implies y x.

Declare Instance implies_reflexive : Reflexive implies.
Declare Instance implies_transitive : Transitive implies.

Declare Instance truth_respects_implies : Proper (implies ==> Basics.impl) truth.
Declare Instance truth_respects_flip_implies : Proper (implies --> Basics.impl) truth.
Declare Instance truth_respects_equivalent : Proper (equivalent ==> iff) truth.

Declare Instance not_respects_implies : Proper (implies --> implies) not | 1.
Declare Instance or_respects_implies : Proper (implies ==> implies ==> implies) or.

Infix "⟹" := implies    (at level 99, right associativity) : boolean_scope.
Infix "≈"  := equivalent (at level 90, no associativity) : boolean_scope.

(** These axioms establish the meaning of the syntactic terms. *)
Axiom impl_def  : forall (p q : t), p ⇒ q ≈ ¬p ∨ q.
Axiom eqv_def   : forall (p q : t), p ≡ q ≈ ¬(¬(p ⇒ q) ∨ ¬(q ⇒ p)).
Axiom true_def  : forall (p : t),   p ∨ ¬p ≈ ⊤.
Axiom false_def : forall (p : t),   ¬(p ∨ ¬p) ≈ ⊥.

(** Clasically [truth p <-> p ≈ ⊤], but constructively this is not the case! *)
Axiom truth_true : truth ⊤.
Axiom not_truth_false : truth ⊥.

(** This is one set of fundamental axioms of boolean algebra.
 *
 * NOTE: It is possible to formulate the following using a single axiom:
 *
 *   forall (p q r s : t),
 *     ¬(¬(¬(p ∨ q) ∨ r) ∨ ¬(p ∨ ¬(¬r ∨ ¬(r ∨ s)))) ≈ r
 *
 * However, the proofs of the three axioms below in terms of this single one
 * are laborious and left as an exercise to the motivated reader. Further
 * notes may be found in the paper "Short Single Axioms for Boolean Algebra"
 * by McCune, et al.
 *)
Axiom or_comm    : forall (p q : t),   p ∨ q ≈ q ∨ p.
Axiom or_assoc   : forall (p q r : t), (p ∨ q) ∨ r ≈ p ∨ (q ∨ r).
Axiom huntington : forall (p q : t),   ¬(¬p ∨ ¬q) ∨ ¬(¬p ∨ q) ≈ p.

End MinimalBooleanLogic.

Module MinimalBooleanLogicFacts (B : MinimalBooleanLogic).

Import B.

Program Instance eqv_equivalence : Equivalence equivalent.
Next Obligation.
  now intro x; split.
Qed.
Next Obligation.
  repeat intro; split; destruct H; now intuition.
Qed.
Next Obligation.
  repeat intro; split; destruct H, H0; now transitivity y.
Qed.

Program Instance implies_respects_implies :
  Proper (implies --> implies ==> Basics.impl) implies.
Next Obligation.
  repeat intro.
  unfold Basics.flip in H.
  now rewrite <- H0, <- H1.
Qed.

Program Instance implies_respects_flip_implies :
  Proper (implies ==> implies --> Basics.flip Basics.impl) implies.
Next Obligation.
  repeat intro.
  unfold Basics.flip in H.
  now rewrite H, H1.
Qed.

Program Instance implies_respects_equivalent :
  Proper (equivalent ==> equivalent ==> Basics.impl) implies.
Next Obligation.
  repeat intro.
  destruct H, H0.
  now rewrite <- H0, <- H1, <- H2.
Qed.

Program Instance not_respects_eqv : Proper (equivalent ==> equivalent) not.
Next Obligation.
  repeat intro.
  destruct H.
  split; intros.
  - now rewrite H0.
  - now rewrite H.
Qed.

Program Instance or_respects_eqv : Proper (equivalent ==> equivalent ==> equivalent) or.
Next Obligation.
  repeat intro.
  destruct H, H0.
  split.
  - now rewrite H, H0.
  - now rewrite H1, H2.
Qed.

Program Instance impl_respects_implies : Proper (implies ==> implies ==> implies) impl.
Next Obligation.
  repeat intro.
  unfold implies.
  rewrite !impl_def.
  rewrite H, H0.
  rewrite <- !impl_def.
  reflexivity.
Qed.

Program Instance impl_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) impl.
Next Obligation.
  repeat intro.
  unfold implies.
  rewrite !impl_def.
  rewrite H, H0.
  rewrite <- !impl_def.
  reflexivity.
Qed.

Program Instance eqv_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) eqv.
Next Obligation.
  repeat intro.
  unfold implies.
  rewrite !eqv_def.
  rewrite H, H0.
  rewrite <- !eqv_def.
  reflexivity.
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

(* Program Instance not_respects_eqv : Proper (eqv ==> eqv) not. *)
(* Program Instance or_respects_eqv : Proper (eqv ==> eqv ==> eqv) or. *)

(** Many of the following proofs are based on work from:
    "A Complete Proof of the Robbins Conjecture", by Allen L. Mann
    May 25, 2003 *)
Theorem or_not (p : t) : p ∨ ¬p ≈ ¬p ∨ ¬¬p.
Proof.
  pose proof (huntington p (¬¬ p)) as H1.
  pose proof (huntington (¬ p) (¬¬ p)) as H2.
  pose proof (huntington (¬ p) (¬ p)) as H3.
  pose proof (huntington (¬¬ p) (¬ p)) as H4.
  rewrite <- H4.
  rewrite <- H3 at 2.
  rewrite <- H2 at 1.
  rewrite <- H1 at 1.
  rewrite <- !or_assoc.
  rewrite (or_comm _ (¬ (¬ ¬ ¬ p ∨ ¬ p))).
  rewrite !or_assoc.
  apply or_respects_eqv.
    now rewrite or_comm.
  rewrite <- !or_assoc.
  rewrite (or_comm _ (¬ (¬ ¬ p ∨ ¬ ¬ p))).
  rewrite !or_assoc.
  apply or_respects_eqv.
    reflexivity.
  apply or_respects_eqv.
    now rewrite or_comm.
  now rewrite or_comm.
Qed.

Theorem not_not (p : t) : ¬¬p ≈ p.
Proof.
  pose proof (huntington (¬¬ p) (¬ p)) as H1.
  pose proof (huntington p (¬¬ p)) as H2.
  rewrite <- H1.
  rewrite (or_comm _ (¬¬p)), <- or_not.
  rewrite or_comm.
  rewrite (or_comm _ (¬p)).
  now apply huntington.
Qed.

Theorem not_swap (p q : t) : ¬p ≈ q <-> p ≈ ¬q.
Proof.
  split; intro.
  - rewrite <- not_not.
    now rewrite H.
  - rewrite H.
    now apply not_not.
Qed.

Theorem not_inj (p q : t) : ¬p ≈ ¬q -> p ≈ q.
Proof.
  intro.
  rewrite <- (not_not p).
  rewrite <- (not_not q).
  now rewrite H.
Qed.

Theorem not_true : ¬⊤ ≈ ⊥.
Proof. now rewrite <- (true_def ⊥), false_def. Qed.

Theorem not_false : ¬⊥ ≈ ⊤.
Proof.
  rewrite <- (false_def ⊤), true_def.
  now apply not_not.
Qed.

Theorem or_false (p : t) : p ∨ ⊥ ≈ p.
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
  rewrite <- (huntington p p) at 2.
  rewrite (or_comm _ p).
  rewrite false_def.
  rewrite <- H4 at 2.
  rewrite <- (false_def p) at 2.
  rewrite <- or_assoc.
  rewrite (or_comm p (¬p)).
  now rewrite huntington.
Qed.

Theorem false_or (p : t) : ⊥ ∨ p ≈ p.
Proof. now rewrite or_comm; apply or_false. Qed.

Theorem or_idem (p : t) : p ∨ p ≈ p.
Proof.
  assert (H1 : forall q, ¬ (¬ q ∨ ¬ q) ≈ q).
    intro q.
    rewrite <- (huntington q q) at 3.
    rewrite (or_comm (¬q) q).
    rewrite false_def.
    now rewrite or_false.
  specialize (H1 (¬p)).
  rewrite not_not in H1.
  apply not_inj.
  exact H1.
Qed.

Theorem or_true (p : t) : p ∨ ⊤ ≈ ⊤.
Proof.
  rewrite <- (true_def p) at 1.
  rewrite <- or_assoc.
  rewrite or_idem.
  now apply true_def.
Qed.

Theorem true_or (p : t) : ⊤ ∨ p ≈ ⊤.
Proof. now rewrite or_comm; apply or_true. Qed.

Theorem not_not_or_true (p : t) : ¬(¬p ∨ ¬⊤) ≈ p.
Proof.
  intros.
  rewrite not_true.
  rewrite or_false.
  now apply not_not.
Qed.

Theorem contrapositive (p q : t) : (p ⟹ q) <-> (¬q ⟹ ¬p).
Proof.
  split; intro.
  - rewrite H.
    reflexivity.
  - apply not_respects_implies in H.
    now rewrite !not_not in H.
Qed.

Theorem or_inj (p q : t) : p ⟹ p ∨ q.
Proof.
  unfold implies.
  rewrite impl_def.
  rewrite <- or_assoc.
  rewrite (or_comm _ p).
  rewrite true_def.
  rewrite true_or.
  exact truth_true.
Qed.

(** Either this or or_inj must be taken as axioms to give insight into ⟹ *)
Theorem impl_implies : forall (p q : t), (p ⟹ q) <-> (⊤ ⟹ p ⇒ q).
Proof.
  split; intros.
  - rewrite <- H.
    rewrite impl_def.
    rewrite or_comm.
    rewrite true_def.
    reflexivity.
  - rewrite <- (huntington p q).
    rewrite impl_def in H.
    rewrite <- H.
    rewrite not_true.
    rewrite or_false.
    apply contrapositive.
    rewrite not_not.
    rewrite or_comm.
    now apply or_inj.
Qed.

Theorem or_inj_r (p q : t) : p ⟹ q ∨ p.
Proof.
  rewrite or_comm.
  now apply or_inj.
Qed.

Theorem true_impl (p : t) : (⊤ ⟹ p) <-> p ≈ ⊤.
Proof.
  split; intro.
  - split; auto.
    rewrite <- (true_def p).
    now apply or_inj.
  - now rewrite H.
Qed.

Theorem impl_true (p : t) : p ⟹ ⊤.
Proof.
  rewrite <- (true_def p).
  now apply or_inj.
Qed.

Theorem false_impl (p : t) : ⊥ ⟹ p.
Proof.
  rewrite <- (false_def p).
  apply contrapositive.
  rewrite not_not.
  rewrite or_comm.
  now apply or_inj.
Qed.

Theorem deduction (p q : t) : (truth p -> truth q) -> (p ⟹ q).
Proof.
  intros.
  unfold implies.
  rewrite impl_def.

End MinimalBooleanLogicFacts.
