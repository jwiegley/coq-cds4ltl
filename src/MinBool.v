Set Warnings "-local-declaration".

Require Import
  Coq.Unicode.Utf8
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid.

(***********************************************************************
 * This is a minimal Boolean Logic comprised of ∨, ¬ and three axioms. *)

Module Type MinimalBooleanLogic.

Parameter t : Type.             (* The type of boolean propositions *)

(** These three terms are syntactic and can be defined in terms of the
    fundamentals above. They are given as parameters so that module authors
    may chose economical definitions; we also provides implies as a relation
    in Prop to facilitate use of Coq's rewriting system. *)
Parameter implies : t -> t -> Prop.
Parameter true    : t.
Parameter false   : t.

#[global]
Declare Instance implies_Reflexive : Reflexive implies.
#[global]
Declare Instance implies_Transitive : Transitive implies.

(** The following are fundamental to a classical definition of this logic. *)
Parameter not : t -> t.
Parameter or  : t -> t -> t.

#[global]
Declare Instance not_respects_implies : Proper (implies --> implies) not.
#[global]
Declare Instance or_respects_implies : Proper (implies ==> implies ==> implies) or.

#[global]
Declare Scope boolean_scope.
Bind Scope boolean_scope with t.
Delimit Scope boolean_scope with boolean.
Open Scope boolean_scope.

Notation "¬ p"   := (not p)   (at level 75, right associativity) : boolean_scope.
Infix    "∨"     := or        (at level 85, right associativity) : boolean_scope.
Notation "p ⇒ q" := (¬ p ∨ q) (at level 86, right associativity) : boolean_scope.
Notation "⊤"     := true      (at level 0, no associativity) : boolean_scope.
Notation "⊥"     := false     (at level 0, no associativity) : boolean_scope.

Definition equivalent p q := implies p q /\ implies q p.

Infix "⟹" := implies    (at level 99, right associativity) : boolean_scope.
Infix "≈"  := equivalent (at level 90, no associativity) : boolean_scope.

(** This is one set of fundamental axioms of boolean algebra.
 *
 * NOTE: It is possible to formulate the following using a single axiom:
 *
 *   ∀ p q r s,
 *     ¬(¬(¬(p ∨ q) ∨ r) ∨ ¬(p ∨ ¬(¬r ∨ ¬(r ∨ s)))) ≈ r
 *
 * However, the proofs of the three axioms below in terms of this single one
 * are laborious and left as an exercise to the motivated reader. Further
 * notes may be found in the paper "Short Single Axioms for Boolean Algebra"
 * by McCune, et al. *)
Axiom or_comm    : ∀ p q,   p ∨ q ≈ q ∨ p.
Axiom or_assoc   : ∀ p q r, (p ∨ q) ∨ r ≈ p ∨ (q ∨ r).
Axiom huntington : ∀ p q,   ¬(¬p ∨ ¬q) ∨ ¬(¬p ∨ q) ≈ p.

(** These axioms establish the meaning of the syntactic terms. *)
Axiom or_inj      : ∀ p q,  p ⟹ p ∨ q.
Axiom true_def    : ∀ p,    p ∨ ¬p ≈ ⊤.
Axiom false_def   : ∀ p,    ¬(p ∨ ¬p) ≈ ⊥.

End MinimalBooleanLogic.

Module MinimalBooleanLogicFacts (Import B : MinimalBooleanLogic).

#[global]
Program Instance equivalent_Equivalence : Equivalence equivalent.
Next Obligation. now intro x; split. Qed.
Next Obligation. repeat intro; split; destruct H; now intuition. Qed.
Next Obligation. repeat intro; split; destruct H, H0; now transitivity y. Qed.

#[global]
Program Instance implies_respects_implies :
  Proper (implies --> implies ==> Basics.impl) implies.
Next Obligation.
  repeat intro.
  unfold Basics.flip in H.
  now rewrite <- H0, <- H1.
Qed.

#[global]
Program Instance implies_respects_equivalent :
  Proper (equivalent ==> equivalent ==> iff) implies.
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros.
  - now rewrite H1, H3, H0.
  - now rewrite <- H2, <- H3, <- H.
Qed.

#[global]
Program Instance equivalent_respects_equivalent :
  Proper (equivalent ==> equivalent ==> iff) equivalent.
Next Obligation.
  repeat intro.
  split; intros.
  - now rewrite <- H, H1, H0.
  - now rewrite H, H1, <- H0.
Qed.

#[global]
Program Instance not_respects_equivalent :
  Proper (equivalent ==> equivalent) not | 9.
Next Obligation.
  repeat intro.
  destruct H.
  split; intros.
  - now rewrite H0.
  - now rewrite H.
Qed.

#[global]
Program Instance or_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) or.
Next Obligation.
  repeat intro.
  destruct H, H0.
  split.
  - now rewrite H, H0.
  - now rewrite H1, H2.
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

#[local] Obligation Tactic := solve [ one_arg | two_arg ].

Theorem or_inj_r p q : p ⟹ q ∨ p.
Proof.
  rewrite or_comm.
  now apply or_inj.
Qed.

Theorem true_impl p : (⊤ ⟹ p) <-> p ≈ ⊤.
Proof.
  split; intro.
  - split; auto.
    rewrite <- (true_def p).
    now apply or_inj.
  - now rewrite H.
Qed.

Theorem impl_true p : p ⟹ ⊤.
Proof.
  rewrite <- (true_def p).
  now apply or_inj.
Qed.

(** Many of the following proofs are based on work from:
    "A Complete Proof of the Robbins Conjecture", by Allen L. Mann
    May 25, 2003 *)
Theorem or_not p : p ∨ ¬p ≈ ¬p ∨ ¬¬p.
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
  apply or_respects_equivalent.
    now rewrite or_comm.
  rewrite <- !or_assoc.
  rewrite (or_comm _ (¬ (¬ ¬ p ∨ ¬ ¬ p))).
  rewrite !or_assoc.
  apply or_respects_equivalent.
    reflexivity.
  apply or_respects_equivalent.
    now rewrite or_comm.
  now rewrite or_comm.
Qed.

Theorem not_not p : ¬¬p ≈ p.
Proof.
  pose proof (huntington (¬¬ p) (¬ p)) as H1.
  pose proof (huntington p (¬¬ p)) as H2.
  rewrite <- H1.
  rewrite (or_comm _ (¬¬p)), <- or_not.
  rewrite or_comm.
  rewrite (or_comm _ (¬p)).
  now apply huntington.
Qed.

Theorem contrapositive p q : (p ⟹ q) <-> (¬q ⟹ ¬p).
Proof.
  split; intro.
  - rewrite H.
    reflexivity.
  - apply not_respects_implies in H.
    now rewrite !not_not in H.
Qed.

Theorem not_swap p q : ¬p ≈ q <-> p ≈ ¬q.
Proof.
  split; intro.
  - rewrite <- not_not.
    now rewrite H.
  - rewrite H.
    now apply not_not.
Qed.

Theorem not_inj p q : ¬p ≈ ¬q -> p ≈ q.
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

Theorem or_false p : p ∨ ⊥ ≈ p.
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

Theorem false_or p : ⊥ ∨ p ≈ p.
Proof. now rewrite or_comm; apply or_false. Qed.

Theorem or_idem p : p ∨ p ≈ p.
Proof.
  assert (H1 : ∀ q, ¬ (¬ q ∨ ¬ q) ≈ q).
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

Theorem or_true p : p ∨ ⊤ ≈ ⊤.
Proof.
  rewrite <- (true_def p) at 1.
  rewrite <- or_assoc.
  rewrite or_idem.
  now apply true_def.
Qed.

Theorem true_or p : ⊤ ∨ p ≈ ⊤.
Proof. now rewrite or_comm; apply or_true. Qed.

(** Either this or or_inj must be taken as an axiom *)
Theorem impl_implies : ∀ p q, (p ⟹ q) <-> (⊤ ⟹ p ⇒ q).
Proof.
  split; intros.
  - rewrite <- H.
    (* rewrite impl_def. *)
    rewrite or_comm.
    rewrite true_def.
    reflexivity.
  - rewrite <- (huntington p q).
    (* rewrite impl_def in H. *)
    rewrite <- H.
    rewrite not_true.
    rewrite or_false.
    apply contrapositive.
    rewrite not_not.
    rewrite or_comm.
    now apply or_inj.
Qed.

Theorem false_impl p : ⊥ ⟹ p.
Proof.
  rewrite <- (false_def p).
  apply contrapositive.
  rewrite not_not.
  rewrite or_comm.
  now apply or_inj.
Qed.

End MinimalBooleanLogicFacts.
