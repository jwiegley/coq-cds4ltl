Set Warnings "-notation-overridden".

Require Import
  Coq.Unicode.Utf8
  Coq.Classes.Morphisms
  MinLTL
  LTL.

(** When we wish to show that there is a sound interpretation of LTL for a
    particular representation, we can either prove the axioms hold under that
    representation, or we can provide functions to denote all terms into a
    simpler model and then show the LTL algebra is homomorphic for that model.
    All the theorems of LTL then follow from the homomorphisms, as shown by
    [DenotationFacts] below. *)
Module Type Denotation (Import L : LinearTemporalLogic).

Parameter A : Type.

Parameter denote : A -> t.

Parameter Top           : A.
Parameter Bottom        : A.
Parameter And           : A -> A -> A.
Parameter Or            : A -> A -> A.
Parameter Not           : A -> A.
Parameter Implies       : A -> A -> Prop.
Parameter Next          : A -> A.
Parameter Until         : A -> A -> A.
Parameter Wait          : A -> A -> A.
Parameter Always        : A -> A.
Parameter Eventually    : A -> A.
Parameter Release       : A -> A -> A.
Parameter StrongRelease : A -> A -> A.

(** Homomorphisms *)

Axiom denote_true           : ⊤ ≈ denote Top.
Axiom denote_false          : ⊥ ≈ denote Bottom.
Axiom denote_and            : ∀ p q, denote p ∧ denote q ≈ denote (And p q).
Axiom denote_or             : ∀ p q, denote p ∨ denote q ≈ denote (Or p q).
Axiom denote_not            : ∀ p, ¬ (denote p) ≈ denote (Not p).
Axiom denote_implies        : ∀ p q, (denote p ⟹ denote q) -> Implies p q.
Axiom denote_next           : ∀ p, ◯ denote p ≈ denote (Next p).
Axiom denote_until          : ∀ p q, denote p U denote q ≈ denote (Until p q).
Axiom denote_wait           : ∀ p q, denote p W denote q ≈ denote (Wait p q).
Axiom denote_always         : ∀ p, □ denote p ≈ denote (Always p).
Axiom denote_eventually     : ∀ p, ◇ denote p ≈ denote (Eventually p).
Axiom denote_release        : ∀ p q, denote p R denote q ≈ denote (Release p q).
Axiom denote_strong_release : ∀ p q, denote p M denote q ≈ denote (StrongRelease p q).

Declare Instance Implies_Reflexive  : Reflexive Implies.
Declare Instance Implies_Transitive : Transitive Implies.

End Denotation.

Module DenotationFacts
       (Import T : LinearTemporalLogic)
       (Import D : Denotation T)
  <: LinearTemporalLogic.

Module Import L   := LinearTemporalLogicFacts T.
Module Import LW  := LinearTemporalLogicWFacts T.
Module Import ML  := MinimalLinearTemporalLogicFacts T.
Module Import BF  := ML.BF.
Module Import MBF := BF.MBF.

Definition t              := A.
Definition true           := Top.
Definition false          := Bottom.
Definition and            := And.
Definition or             := Or.
Definition not            := Not.
Definition implies        := Implies.
Definition equivalent     := λ p q, implies p q /\ implies q p.
Definition next           := Next.
Definition until          := Until.
Definition wait           := Wait.
Definition always         := Always.
Definition eventually     := Eventually.
Definition release        := Release.
Definition strong_release := StrongRelease.

Instance implies_Reflexive      : Reflexive  implies := Implies_Reflexive.
Instance implies_Transitive     : Transitive implies := Implies_Transitive.
Instance equivalent_Equivalence : Equivalence equivalent.
Proof.
  unfold equivalent.
  split; repeat intro; intuition;
  now transitivity y.
Qed.

Ltac defer H :=
  repeat intro;
  unfold Basics.flip in *;
  first [ apply denote_implies
        | split; apply denote_implies
        ];
  repeat first
         [ rewrite <- denote_true
         | rewrite <- denote_false
         | rewrite <- denote_and
         | rewrite <- denote_or
         | rewrite <- denote_not
         | rewrite <- denote_next
         | rewrite <- denote_until
         | rewrite <- denote_wait
         | rewrite <- denote_always
         | rewrite <- denote_eventually
         | rewrite <- denote_release
         | rewrite <- denote_strong_release
         | rewrite <- denote_not
         ];
  try apply H; auto;
  try apply denote_implies; auto.

Declare Instance denote_respects_implies : Proper (Implies ==> T.implies) denote.

Program Instance not_respects_implies : Proper (implies --> implies) not | 1.
Next Obligation. defer not_respects_implies; now rewrite H. Qed.

Program Instance and_respects_implies :
  Proper (implies ==> implies ==> implies) and.
Next Obligation. defer and_respects_implies; now rewrite ?H, ?H0. Qed.

Program Instance or_respects_implies :
  Proper (implies ==> implies ==> implies) or.
Next Obligation. defer or_respects_implies; now rewrite ?H, ?H0. Qed.

Program Instance next_respects_implies :
  Proper (implies ==> implies) next.
Next Obligation. defer next_respects_implies; now rewrite H. Qed.

Program Instance until_respects_implies :
  Proper (implies ==> implies ==> implies) until.
Next Obligation. defer until_respects_implies; now rewrite ?H, ?H0. Qed.

Program Instance wait_respects_implies :
  Proper (implies ==> implies ==> implies) wait.
Next Obligation. defer wait_respects_implies; now rewrite ?H, ?H0. Qed.

Program Instance eventually_respects_implies :
  Proper (implies ==> implies) eventually.
Next Obligation. defer eventually_respects_implies; now rewrite H. Qed.

Program Instance always_respects_implies :
  Proper (implies ==> implies) always.
Next Obligation. defer always_respects_implies; now rewrite H. Qed.

Program Instance release_respects_implies :
  Proper (implies ==> implies ==> implies) release.
Next Obligation. defer release_respects_implies; now rewrite ?H, ?H0. Qed.

Program Instance strong_release_respects_implies :
  Proper (implies ==> implies ==> implies) strong_release.
Next Obligation. defer strong_release_respects_implies; now rewrite ?H, ?H0. Qed.

(** Since the algebraic homomorpmisms were proven above, all the theorems of
    our algebra/logic trivially follow. *)

Declare Scope boolean_scope.
Bind Scope boolean_scope with t.
Delimit Scope boolean_scope with boolean.
Open Scope boolean_scope.

Notation "¬ p"    := (not p)         (at level 75, right associativity) : boolean_scope.
Infix    "∨"      := or              (at level 85, right associativity) : boolean_scope.
Notation "p ⇒ q"  := (¬ p ∨ q)       (at level 86, right associativity) : boolean_scope.
Notation "⊤"      := true            (at level 0, no associativity) : boolean_scope.
Notation "⊥"      := false           (at level 0, no associativity) : boolean_scope.
Infix    "∧"      := and             (at level 80, right associativity) : boolean_scope.
Infix    "⟹"     := implies         (at level 99, right associativity) : boolean_scope.
Infix    "≈"      := equivalent      (at level 90, no associativity) : boolean_scope.

Declare Scope ltl_scope.
Bind Scope ltl_scope with t.
Delimit Scope ltl_scope with ltl.
Open Scope boolean_scope.
Open Scope ltl_scope.

Notation "◯ p"       := (next p)             (at level 75, right associativity) : ltl_scope.
Notation "◇ p"       := (eventually p)       (at level 75, right associativity) : ltl_scope.
Notation "□ p"       := (always p)           (at level 75, right associativity) : ltl_scope.
Notation "p 'U' q"   := (until p q)          (at level 79, right associativity) : ltl_scope.
Notation "p 'W' q"   := (wait p q)           (at level 79, right associativity) : ltl_scope.
Notation "p 'R' q"   := (release p q)        (at level 79, right associativity) : ltl_scope.
Notation "p 'M' q"   := (strong_release p q) (at level 79, right associativity) : ltl_scope.

Theorem or_inj p q : p ⟹ p ∨ q.
Proof. defer or_inj. Qed.

Theorem true_def p : p ∨ ¬p ≈ ⊤.
Proof. defer true_def. Qed.

Theorem false_def p : ¬(p ∨ ¬p) ≈ ⊥.
Proof. defer false_def. Qed.

Theorem or_comm p q : p ∨ q ≈ q ∨ p.
Proof. defer or_comm. Qed.

Theorem or_assoc p q r : (p ∨ q) ∨ r ≈ p ∨ (q ∨ r).
Proof. defer or_assoc. Qed.

Theorem and_def p q : p ∧ q ≈ ¬(¬p ∨ ¬q).
Proof. defer and_def. Qed.

Theorem huntington p q : ¬(¬p ∨ ¬q) ∨ ¬(¬p ∨ q) ≈ p.
Proof. defer huntington. Qed.

Theorem (* 1 *) next_not p : ◯ ¬p ≈ ¬◯ p.
Proof. defer next_not. Qed.

Theorem (* 2 *) next_impl p q : ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Proof. defer next_impl. Qed.

Theorem (* 10 *) until_expand p q : p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Proof. defer until_expand. Qed.

Theorem (* 9 *) next_until p q : ◯ (p U q) ≈ (◯ p) U (◯ q).
Proof. defer next_until. Qed.

Theorem (* 11 *) until_false p : p U ⊥ ≈ ⊥.
Proof. defer until_false. Qed.

Theorem (* NEW *) looped p : ◯ ¬p U p ≈ p.
Proof. defer looped. Qed.

Theorem (* 12 *) until_left_or p q r : p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Proof. defer until_left_or. Qed.

Theorem (* 14 *) until_left_and p q r : p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Proof. defer until_left_and. Qed.

Theorem (* NEW *) until_and_until p q r s :
  (p U q) ∧ (r U s) ⟹ (p ∧ r) U ((q ∧ r) ∨ (p ∧ s) ∨ (q ∧ s)).
Proof. defer until_and_until. Qed.

Theorem (* 17 *) until_left_or_order p q r : p U (q U r) ⟹ (p ∨ q) U r.
Proof. defer until_left_or_order. Qed.

Theorem (* 18 *) until_right_and_order p q r : p U (q ∧ r) ⟹ (p U q) U r.
Proof. defer until_right_and_order. Qed.

Theorem (* 170 *) not_until p q : ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).
Proof. defer not_until. Qed.

Theorem (* 38 *) evn_def p : ◇ p ≈ ⊤ U p.
Proof. defer evn_def. Qed.

Theorem (* 54 *) always_def p : □ p ≈ ¬◇ ¬p.
Proof. defer always_def. Qed.

Theorem (* 169 *) wait_def p q : p W q ≈ □ p ∨ p U q.
Proof. defer wait_def. Qed.

Theorem release_def p q : p R q ≈ ¬(¬p U ¬q).
Proof. defer release_def. Qed.

Theorem strong_release_def p q : p M q ≈ q U (p ∧ q).
Proof. defer strong_release_def. Qed.

End DenotationFacts.
