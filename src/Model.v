Require Import
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Classes.SetoidClass
  Coq.Logic.Classical
  Coq.Program.Program
  Coq.Relations.Relation_Definitions
  Coq.Setoids.Setoid
  Coq.Sets.Classical_sets
  Coq.Sets.Ensembles
  Stream
  Same_set.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Module Type Boolean.

Parameter t : Type.

Parameter impl : t -> t -> Prop.
Parameter equiv : t -> t -> Prop.
Parameter true : t.
Parameter false : t.
Parameter not : t -> t.
Parameter or : t -> t -> t.
Parameter and : t -> t -> t.

Declare Instance impl_transitive : Transitive impl.
Declare Instance impl_equiv : Proper (equiv ==> equiv ==> Basics.impl) impl.
Declare Instance impl_flip : Proper (impl --> equiv ==> flip Basics.impl) impl.
Declare Instance equiv_equivalence : Equivalence equiv.
Declare Instance equiv_equiv : Proper (equiv ==> equiv ==> Basics.impl) equiv.
Declare Instance equiv_flip_equiv : Proper (equiv ==> equiv ==> flip Basics.impl) equiv.
Declare Instance not_equiv : Proper (equiv ==> equiv) not.
Declare Instance or_equiv : Proper (equiv ==> equiv ==> equiv) or.
Declare Instance and_equiv : Proper (equiv ==> equiv ==> equiv) and.

Global Infix    "⟹"      := impl            (at level 91).
Global Infix    "≈"       := equiv           (at level 90).
Global Notation "⊤"       := true            (at level 0).
Global Notation "⊥"       := false           (at level 0).
Global Notation "¬ p"     := (not p)         (at level 0).
Global Infix    "∨"       := or              (at level 46, right associativity).
Global Infix    "∧"       := and             (at level 45, right associativity).
Global Notation "p → q"   := (¬ p ∨ q)       (at level 80, only parsing).
Global Notation "p ↔ q"   := (p → q ∧ q → p) (at level 80, only parsing).
Global Notation "p ≡ q"   := (p ↔ q)         (at level 80, only parsing).

(** "and" is not fundamental, and can be defined in terms of "or". To allow
    for efficient choices of "and", we simply require that its behavior be
    equivalent to the more basic definition. *)
Hypothesis impl_def : forall (φ ψ : t), φ ⟹ ψ <-> φ → ψ ≈ ⊤.
Hypothesis equiv_def : forall (φ ψ : t), φ ≈ ψ <-> (φ ⟹ ψ) /\ (ψ ⟹ φ).
Hypothesis true_def : forall (φ : t), ⊤ ≈ φ ∨ ¬ φ.
Hypothesis false_def : forall (φ : t), ⊥ ≈ ¬ (φ ∨ ¬ φ).
Hypothesis and_def : forall (φ ψ : t), φ ∧ ψ ≈ ¬ (¬ φ ∨ ¬ ψ).

(** This is one set of fundamental axioms of boolean algebra. *)
Hypothesis not_not : forall (φ : t), ¬¬ φ ≈ φ.
Hypothesis or_true : forall (φ : t), φ ∨ ⊤ ≈ ⊤.
Hypothesis or_false : forall (φ : t), φ ∨ ⊥ ≈ φ.
Hypothesis or_idem : forall (φ : t), φ ∨ φ ≈ φ.
Hypothesis or_comm : forall (φ ψ : t), φ ∨ ψ ≈ ψ ∨ φ.
Hypothesis or_assoc : forall (φ ψ χ : t), (φ ∨ ψ) ∨ χ ≈ φ ∨ (ψ ∨ χ).
Hypothesis distr_or_and : forall (φ ψ χ : t), φ ∧ (ψ ∨ χ) ≈ (φ ∧ ψ) ∨ (φ ∧ χ).
Hypothesis distr_and_or : forall (φ ψ χ : t), φ ∨ (ψ ∧ χ) ≈ (φ ∨ ψ) ∧ (φ ∨ χ).

Lemma not_true : ¬ ⊤ ≈ ⊥.
Proof.
  rewrite (true_def ⊥).
  now rewrite <- false_def.
Qed.

Lemma not_false : ¬ ⊥ ≈ ⊤.
Proof.
  rewrite <- not_true.
  now apply not_not.
Qed.

Lemma impl_true (φ : t) : ⊤ ⟹ φ <-> φ ≈ ⊤.
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

Lemma contrapositive (φ ψ : t) : φ ⟹ ψ -> ¬ ψ ⟹ ¬ φ.
Proof.
  intro.
  apply impl_def.
  rewrite not_not.
  rewrite or_comm.
  now apply (proj1 (impl_def _ _)).
Qed.

Lemma absurdity (φ : t) : φ ∧ ¬ φ ⟹ ⊥.
Proof.
  rewrite and_def.
  apply impl_def.
  rewrite !not_not.
  rewrite (or_comm _ φ).
  rewrite <- true_def.
  rewrite <- not_true.
  now rewrite <- true_def.
Qed.

Lemma not_or (φ ψ : t) : ¬ (φ ∨ ψ) ≈ ¬ φ ∧ ¬ ψ.
Proof.
  rewrite and_def.
  now rewrite !not_not.
Qed.

Lemma not_and (φ ψ : t) : ¬ (φ ∧ ψ) ≈ ¬ φ ∨ ¬ ψ.
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
  rewrite <- distr_or_and.
  rewrite or_comm.
  rewrite or_true.
  now rewrite and_true.
Qed.

Lemma and_absorb (φ ψ : t) : φ ∧ (φ ∨ ψ) ≈ φ.
Proof.
  rewrite <- (or_false φ) at 1.
  rewrite <- distr_and_or.
  rewrite and_comm.
  rewrite and_false.
  now rewrite or_false.
Qed.

Lemma weakening (φ ψ : t) : φ ⟹ φ ∨ ψ.
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

End Boolean.

Module Type LTL <: Boolean.

(***********************************************************************
 *
 * This logic follows directly the paper
 *
 * "A Calculational Deductive System for Linear Temporal Logic"
 *
 * by Warford, Vega and Staley, https://dl.acm.org/doi/10.1145/3387109
 *)

Include Boolean.

Parameter next : t -> t.
Parameter until : t -> t -> t.

Declare Instance next_equiv : Proper (equiv ==> equiv) next.
Declare Instance until_equiv : Proper (equiv ==> equiv ==> equiv) until.

Global Notation "◯ p"     := (next p)    (at level 0).
Global Notation "p 'U' q" := (until p q) (at level 45).

(*** 3.1 Next *)

Hypothesis (* 1 *) next_self_dual : forall (φ : t), ◯¬ φ ≈ ¬◯ φ.
Hypothesis (* 2 *) next_distr_impl : forall (φ ψ : t), ◯ (φ → ψ) ≈ ◯ φ → ◯ ψ.

Lemma (* 3 *) next_linearity (φ : t) : ◯ φ ≈ ¬◯¬ φ.
Proof.
  rewrite next_self_dual.
  now apply not_swap.
Qed.

Lemma (* 4 *) next_distr_or (φ ψ : t) : ◯ (φ ∨ ψ) ≈ ◯ φ ∨ ◯ ψ.
Proof.
  pose proof (next_distr_impl (¬ φ) ψ) as H; rewrite not_not in H.
  rewrite H.
  now rewrite <- next_linearity.
Qed.

Lemma (* 5 *) next_distr_and (φ ψ : t) : ◯ (φ ∧ ψ) ≈ ◯ φ ∧ ◯ ψ.
Proof.
  rewrite <- (not_not φ) at 1.
  rewrite <- (not_not ψ) at 1.
  rewrite <- not_or.
  rewrite next_self_dual.
  rewrite next_distr_or.
  rewrite not_or.
  now rewrite <- !next_linearity.
Qed.

Lemma (* 6 *) next_distr_next_eq (φ ψ : t) : ◯ (φ ≡ ψ) ≈ ◯ φ ≡ ◯ ψ.
Proof.
  rewrite next_distr_or.
  rewrite not_or.
  rewrite next_distr_and.
  rewrite next_self_dual.
  rewrite next_self_dual.
  rewrite not_and.
  rewrite next_distr_or.
  rewrite next_self_dual.
  rewrite <- not_and.
  now rewrite <- not_or.
Qed.

Lemma (* 7 *) next_top : ◯ (⊤) ≈ ⊤.
Proof.
  rewrite (true_def ⊤) at 1.
  rewrite next_distr_or.
  rewrite next_self_dual.
  now rewrite <- true_def.
Qed.

Lemma (* 8 *) next_bottom : ◯ (⊥) ≈ ⊥.
Proof.
  rewrite (false_def ⊥) at 1.
  rewrite next_self_dual.
  rewrite next_distr_or.
  rewrite next_self_dual.
  now rewrite <- false_def.
Qed.

(*** 3.2 Until *)

Hypothesis (* 9 *) next_distr_until : forall (φ ψ : t), ◯ (φ U ψ) ≈ (◯ φ) U (◯ ψ).
Hypothesis (* 10 *) until_expansion : forall (φ ψ : t), φ U ψ ≈ ψ ∨ (φ ∧ ◯ (φ U ψ)).
Hypothesis (* 11 *) until_right_bottom : forall (φ : t), φ U ⊥ ≈ ⊥.
Hypothesis (* 12 *) until_left_distr_or : forall (φ ψ χ : t), φ U (ψ ∨ χ) ≈ (φ U ψ) ∨ (φ U χ).
Hypothesis (* 13 *) until_right_distr_or : forall (φ ψ χ : t), (φ U χ) ∨ (ψ U χ) ⟹ (φ ∨ ψ) U χ.
Hypothesis (* 14 *) until_left_distr_and : forall (φ ψ χ : t), φ U (ψ ∧ χ) ⟹ (φ U ψ) ∧ (φ U χ).
Hypothesis (* 15 *) until_right_distr_and : forall (φ ψ χ : t), (φ ∧ ψ) U χ ≈ (φ U χ) ∧ (ψ U χ).
Hypothesis (* 16 *) until_impl_order : forall (φ ψ χ : t), (φ U ψ) ∧ (¬ ψ U χ) ⟹ φ U χ.
Hypothesis (* 17 *) until_right_or_order : forall (φ ψ χ : t), φ U (ψ U χ) ⟹ (φ ∨ ψ) U χ.
Hypothesis (* 18 *) until_right_and_order : forall (φ ψ χ : t), φ U (ψ ∧ χ) ⟹ φ U (ψ U χ).

(* Lemmas 19-37 *)

Lemma (* 19 *) until_right_distr_impl (φ ψ χ : t) : (φ → ψ) U χ ⟹ (φ U χ) → (ψ U χ).
Proof.
  rewrite <- until_right_distr_or.
  rewrite <- !weakening.
Admitted.

Lemma (* 20 *) until_right_top (φ : t) : φ U ⊤ ≈ ⊤.
Admitted.

Lemma (* 21 *) until_left_bottom (φ : t) : ⊥ U φ ≈ φ.
Admitted.

Lemma (* 22 *) until_idempotency (φ : t) : φ U φ ≈ φ.
Proof.
  rewrite until_expansion.
  now rewrite or_absorb.
Qed.

Lemma (* 23 *) until_excl_middle (φ ψ : t) : (φ U ψ) ∨ (φ U ¬ ψ) ≈ ⊤.
Admitted.

Lemma (* 24 *) until_24 (φ ψ χ : t) : (¬ φ U (ψ U χ)) ∧ (φ U χ) ⟹ ψ U χ.
Admitted.

Lemma (* 25 *) until_25 (φ ψ χ : t) : (φ U (¬ ψ U χ)) ∧ (ψ U χ) ⟹ φ U χ.
Admitted.

Lemma (* 26 *) until_26 (φ ψ : t) : (φ U ψ) ∧ (¬ ψ U φ) ⟹ φ.
Admitted.

Lemma (* 27 *) until_27 (φ ψ : t) : φ ∧ (¬ φ U ψ) ⟹ ψ.
Admitted.

Lemma (* 28 *) until_28 (φ ψ : t) : φ U ψ ⟹ φ ∨ ψ.
Admitted.

Lemma (* 29 *) until_insertion (φ ψ : t) : ψ ⟹ φ U ψ.
Proof.
  rewrite until_expansion.
  now apply weakening.
Qed.

Lemma (* 30 *) until_30 (φ ψ : t) : φ ∧ ψ ⟹ φ U ψ.
Admitted.

Lemma (* 31 *) until_absorb_or_u (φ ψ : t) : φ ∨ (φ U ψ) ≈ φ ∨ ψ.
Admitted.

Lemma (* 32 *) until_absorb_u_or (φ ψ : t) : (φ U ψ) ∨ ψ ≈ φ U ψ.
Admitted.

Lemma (* 33 *) until_absorb_u_and (φ ψ : t) : (φ U ψ) ∧ ψ ≈ ψ.
Admitted.

Lemma (* 34 *) until_absorb_u_or_and (φ ψ : t) : (φ U ψ) ∨ (φ ∧ ψ) ≈ φ U ψ.
Admitted.

Lemma (* 35 *) until_absorb_u_and_or (φ ψ : t) : (φ U ψ) ∧ (φ ∨ ψ) ≈ φ U ψ.
Admitted.

Lemma (* 36 *) until_left_absorb (φ ψ : t) : φ U (φ U ψ) ≈ φ U ψ.
Admitted.

Lemma (* 37 *) until_right_absorb (φ ψ : t) : (φ U ψ) U ψ ≈ φ U ψ.
Admitted.

End LTL.

Module Type ExtendedLTL <: LTL.

Include LTL.

Parameter eventually : t -> t.
Parameter always : t -> t.
Parameter wait : t -> t -> t.
Parameter release : t -> t -> t.

Declare Instance eventually_equiv : Proper (equiv ==> equiv) eventually.
Declare Instance always_equiv : Proper (equiv ==> equiv) always.
Declare Instance wait_equiv : Proper (equiv ==> equiv ==> equiv) wait.
Declare Instance release_equiv : Proper (equiv ==> equiv ==> equiv) release.

Global Notation "◇ p"     := (eventually p)  (at level 0).
Global Notation "□ p"     := (always p)      (at level 0).
Global Notation "p 'W' q" := (wait p q)      (at level 45).
Global Notation "p 'R' q" := (release p q)   (at level 45).

(*** 3.3 Eventually *)

(* Axiom 38 *)
(* Lemmas 39-53 *)

Hypothesis (* 38 *) eventually_def : forall (φ : t), ◇ φ ≈ ⊤ U φ.

(*** 3.4 Always *)

(* Lemmas 57-81 *)

Hypothesis (* 54 *) always_def : forall (φ : t), □ φ ≈ ¬◇¬ φ.
Hypothesis (* 55 *) always_until_ind : forall (φ ψ χ : t), □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ φ → □ ψ ∨ (ψ U χ).
Hypothesis (* 56 *) always_until_ind2 : forall (φ ψ : t), □ (φ → ◯ (φ ∨ ψ)) ⟹ φ → □ φ ∨ (φ U ψ).

(*** 3.5 Temporal Deduction *)

(* Lemma 82 *)

(*** 3.6 Always, Continued *)

(* Lemmas 83-135 *)

(*** 3.7 Proof Metatheorems *)

(* Lemmas 136-139 *)

(*** 3.8 Always, Continued *)

(* Lemmas 140-168 *)

(*** 3.9 Wait *)

(* Axioms 169-170 *)
(* Lemmas 171-254 *)

Hypothesis (* 169 *) wait_def : forall (φ ψ : t), φ W ψ ≈ □ φ ∨ (φ U ψ).
Hypothesis (* 170 *) wait_distr_not : forall (φ ψ : t), ¬(φ W ψ) ≈ ¬ ψ U (¬ φ ∧ ¬ ψ).

End ExtendedLTL.

Module StreamLTL <: ExtendedLTL.

Variable a : Type.

Definition t := Ensemble (Stream a).

Definition equiv := Same_set (Stream a).
Definition not := Complement (Stream a).
Definition and := Intersection (Stream a).
Definition or := Union (Stream a).

Definition next (p : t) : t := fun s => p (tail s).
Definition until (p q : t) : t :=
  fun s => exists i, q (from i s) /\ forall k, k < i -> p (from k s).

Ltac solve :=
  repeat
    (match goal with
     | [ H : () |- _ ] => destruct H
     | [ |- _ ≈ _ ] => split; repeat intro

     | [ H : (_ ∧ _) _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- (_ ∧ _) _ ] => split

     | [ H : (_ ∨ _) _ |- _ ] =>
       let H1 := fresh "H" in inversion H as [H1|H1]; subst; clear H
     | [ H : ?P _ |- (?P ∨ _) _ ] => now left
     | [ H : ?P _ |- (_ ∨ ?P) _ ] => now right
     | [ H : ?P _ |- ((?P ∨ _) ∨ _) _ ] => now left; left
     | [ H : ?P _ |- ((_ ∨ ?P) ∨ _) _ ] => now left; right
     | [ H : ?P _ |- (_ ∨ (?P ∨ _)) _ ] => now right; left
     | [ H : ?P _ |- (_ ∨ (_ ∨ ?P)) _ ] => now right; right
     | [ H : ¬ ?P _ |- (¬ ?P ∨ _) _ ] => now left
     | [ H : ¬ ?P _ |- (_ ∨ ¬ ?P) _ ] => now right
     | [ H : ¬ ?P _ |- ((¬ ?P ∨ _) ∨ _) _ ] => now left; left
     | [ H : ¬ ?P _ |- ((_ ∨ ¬ ?P) ∨ _) _ ] => now left; right
     | [ H : ¬ ?P _ |- (_ ∨ (¬ ?P ∨ _)) _ ] => now right; left
     | [ H : ¬ ?P _ |- (_ ∨ (_ ∨ ¬ ?P)) _ ] => now right; right

     | [ H1 : ?P _, H2 : ?Q _ |- ((?P ∧ ?Q) ∨ _) _ ] => left
     | [ H1 : ?P _, H2 : ?Q _ |- (_ ∨ (?P ∧ ?Q)) _ ] => right

     | [ H : ¬ (_ ∨ _) _ |- _ ] => apply not_or in H
     | [ H : ¬ (_ ∧ _) _ |- _ ] => apply not_and in H

     | [ H : _ /\ _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- _ /\ _ ] => split

     | [ H : _ \/ _ |- _ ] =>
       let H1 := fresh "H" in inversion H as [H1|H1]; subst; clear H

     | [ H : (_ ↔ _) _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- (_ ↔ _) _ ] => split

     | [ |- _ -> _ ] => intro
     | [ H: ?P |- ?P ] => apply H

     | [ H : ?P ≈ ?Q |- _ ] => rewrite H in *; clear H

     | [ H : _ <-> _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- _ <-> _ ] => split

     | [ H1 : ?P, H2 : ~ ?P |- _ ] => contradiction
     | [ H1 : ?P _, H2 : ¬ ?P _ |- _ ] => contradiction

     | [ H : (⊥) _ |- _ ] => contradiction
     | [ H : ¬ (⊤) _ |- False ] => apply H

     | [ |- (⊤) _ ] => now constructor
     | [ |- ¬ _ _ ] => intro
     | [ |- (⊥) _ ] => elimtype False
     | [ |- ~ _ ] => intro
     | [ H : ¬ (fun _ => forall _, _) _ |- _ ] => unfold Complement, In in H

     | [ |- ◯ _ _ ] => unfold next

     | [ |- nat ] => exact 0

     | [ H : ~ (forall _, ~ _)        |- _ ] => apply not_all_not_ex in H
     | [ H : (forall _, ~ _) -> False |- _ ] => apply not_all_not_ex in H
     | [ H : ~ (forall _, _)          |- _ ] => apply not_all_ex_not in H
     | [ H : (forall _, _) -> False   |- _ ] => apply not_all_ex_not in H
     | [ H : ~ (exists _, ~ _)        |- _ ] => apply not_ex_not_all in H
     | [ H : (exists _, ~ _) -> False |- _ ] => apply not_ex_not_all in H
     | [ H : ~ (exists _, _)          |- _ ] => apply not_ex_all_not in H
     | [ H : (exists _, _) -> False   |- _ ] => apply not_ex_all_not in H

     | [ |- exists _, ¬ _ _ ] => apply not_all_ex_not; intro

     | [ H : forall i : nat, ?P (from i ?S) |- ?P ?S ] => apply (H 0)
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (tail ?S) ] => apply (H 1)
     | [ H : ?P ?S |- exists i : nat, ?P (from i ?S) ] => exists 0
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (from ?I (tail ?S)) ]
         => rewrite from_tail_S; apply H
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (tail (from ?I ?S)) ]
         => rewrite tail_from_S; apply H
     | [ H : ?P (tail ?S) |- exists i : nat, ?P (from i ?S) ] => exists 1
     | [ H : forall i : nat, ?P (from i (from ?X ?S))
       |- exists n : nat, ?P (from n (from _ ?S)) ] => eexists; rewrite from_from
     | [ H : forall i : nat, ?P (from i (tail ?S)) |- ?P (tail (from _ ?S)) ] =>
       rewrite tail_from
     | [ H : forall i : nat, ?P (tail (from i ?S)) |- ?P (from _ (tail ?S)) ] =>
       rewrite from_tail
     | [ H : forall i j : nat, ?P (from j (from i ?S)) |- ?P (from _ ?S) ] =>
       apply (H 0)
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (from ?I (from ?J ?S)) ] =>
       rewrite from_plus
     | [ H : ?P (from ?I (from ?J ?S)) |- exists i : nat, ?P (from i ?S) ] =>
       rewrite from_plus in H
     | [ H : ?P (from ?I ?S) |- exists i : nat, ?P (from i ?S) ] => exists I
     | [ H : ?P (from ?I ?S) |- exists i j : nat, ?P (from i (from j ?S)) ] =>
       exists I; exists 0
     | [ H : ?P (from ?I ?S) |- exists i j : nat, ?P (from j (from i ?S)) ] =>
       exists I; exists 0
     | [ H : ?P (tail (from ?I ?S)) |- exists i : nat, ?P (from i (tail ?S)) ] =>
       exists I; rewrite from_tail
     | [ H : ?P (from ?I (tail ?S)) |- exists i : nat, ?P (tail (from i ?S)) ] =>
       exists I; rewrite tail_from

     end;
     unfold In, next, until, any, every, release, weakUntil in *;
     intros;
     try rewrite !Complement_Complement in *;
     try unshelve intuition eauto;
     try unshelve firstorder eauto;
     try unshelve eauto;
     try (now left);
     try (now right);
     try (now left; left);
     try (now left; right);
     try (now right; left);
     try (now right; right)).

Hypothesis (* 1 *) next_self_dual : forall (φ : Formula), ◯¬ φ ≈ ¬◯ φ.
Hypothesis (* 2 *) next_distr_impl : forall (φ ψ : Formula), ◯ (φ → ψ) ≈ ◯ φ → ◯ ψ.

End StreamLTL.

(** Boolean logic *)

Infix    "≈"     := (Same_set (Stream a))     (at level 100).
Notation "p ≉ q" := (~ (p ≈ q))               (at level 100).
Notation "⊤"     := (Full_set (Stream a))     (at level 45).
Notation "⊥"     := (Empty_set (Stream a))    (at level 45).
Infix    "∧"     := (Intersection (Stream a)) (at level 45).
Infix    "∨"     := (Union (Stream a))        (at level 45).
Notation "¬ p"   := (Complement (Stream a) p) (at level 0).
Notation "p → q" := (¬ p ∨ (p ∧ q))           (at level 45).
Notation "p ↔ q" := ((p → q) ∧ (q → p))       (at level 45).

Lemma not_inj (φ ψ : LTL) : (φ ≈ ψ) -> ¬φ ≈ ¬ψ.
Proof. intros; now rewrite H. Qed.

(* DeMorgan's laws *)
Lemma not_or (φ ψ : LTL) : ¬ (φ ∨ ψ) ≈ ¬ φ ∧ ¬ ψ.
Proof.
  split.
  - intros s NAB.
    split.
    + intro.
      apply NAB.
      left; auto.
    + intro.
      apply NAB.
      right; auto.
  - intros s NAB.
    intro.
    induction NAB.
    destruct H.
    + apply H0; auto.
    + apply H1; auto.
Qed.

Lemma not_and (φ ψ : LTL) : ¬ (φ ∧ ψ) ≈ ¬ φ ∨ ¬ ψ.
Proof.
  split.
  - rewrite <- Complement_Complement.
    intros s NAB.
    intro H.
    apply NAB.
    split.
    + rewrite <- (Complement_Complement _ φ).
      intro H0.
      apply H.
      left; auto.
    + rewrite <- (Complement_Complement _ ψ).
      intro H0.
      apply H.
      right; auto.
  - intros s NANB AB.
    destruct AB as [A1 B1].
    destruct NANB as [s NA | s NB]; auto.
Qed.

(** ◯ (or X) - next *)

Definition next (p : LTL) : LTL := fun s => p (tail s).

Notation "◯ p" := (next p) (at level 0).

Global Program Instance next_Same_set:
  Proper (Same_set (Stream a) ==> Same_set (Stream a)) next.
Next Obligation.
  split; repeat intro; unfold In, next in *; now apply H.
Qed.

Global Program Instance next_Same_set_iff (p : LTL) :
  Proper (stream_eq a ==> iff) p ->
  Proper (stream_eq a ==> iff) (next p).
Next Obligation.
  split; repeat intro.
  - unfold next in *.
    now setoid_rewrite <- H0.
  - unfold next in *.
    now setoid_rewrite H0.
Qed.

Lemma next_inv (p : LTL) (s : Stream a) :
  next p s -> exists x s', stream_eq a s (Cons x s') /\ p s'.
Proof.
  unfold next, tail.
  intros.
  exists (head s).
  exists (tail s).
  split.
  - unfold head, tail; intros.
    now destruct s.
  - exact H.
Qed.

Lemma next_cons_inv (p : LTL) x s : next p (Cons x s) <-> p s.
Proof. now unfold next, tail. Qed.

(** p U q - until *)

Definition until (p q : LTL) : LTL :=
  fun s => exists i, q (from i s) /\ forall k, k < i -> p (from k s).

Notation "p 'U' q" := (until p q) (at level 45).

Global Program Instance until_Same_set :
  Proper (Same_set (Stream a) ==> Same_set (Stream a)
                              ==> Same_set (Stream a)) until.
Next Obligation.
  intros.
  split; repeat intro; unfold In in *.
  - destruct H1, H1.
    exists x2.
    split.
    + now apply H0.
    + intros.
      now apply H, H2.
  - destruct H1, H1.
    exists x2.
    split.
    + now apply H0.
    + intros.
      now apply H, H2.
Qed.

Global Program Instance until_Same_set_iff (p q : LTL) :
  Proper (stream_eq a ==> iff) p ->
  Proper (stream_eq a ==> iff) q ->
  Proper (stream_eq a ==> iff) (until p q).
Next Obligation.
  unfold until.
  split; repeat intro.
  - destruct H2, H2.
    exists x0.
    split.
    + now setoid_rewrite <- H1.
    + intros.
      setoid_rewrite <- H1.
      now apply H3.
  - destruct H2, H2.
    exists x0.
    split.
    + now setoid_rewrite H1.
    + intros.
      setoid_rewrite H1.
      now apply H3.
Qed.

Lemma until_inv (p q : LTL) s :
  until p q s -> q s \/ (p s /\ until p q (tail s)).
Proof.
  intros.
  dependent induction H; intuition.
Admitted.

Lemma until_cons_inv (p q : LTL) x s :
  until p q (Cons x s) -> q (Cons x s) \/ (p (Cons x s) /\ until p q s).
Proof.
  intros.
  dependent induction H; intuition.
Admitted.

Notation "□ p" := (every p) (at level 0).
Notation "◇ p" := (any p) (at level 0).

Definition weakUntil (p q : LTL) := (p U q) ∨ □ p.
Notation "p 'W' q" := (weakUntil p q) (at level 40).

Definition release (p q : LTL) := ¬(¬p U ¬q).
Notation "p 'R' q" := (release p q) (at level 40).

Definition strongRelease (p q : LTL) := (p R q) ∧ ◇ p.
Notation "p 'M' q" := (strongRelease p q) (at level 40).

(*************************************************************************
 * Laws for the Linear Temporal Logic
 *)

Ltac solve :=
  repeat
    (match goal with
     | [ H : () |- _ ] => destruct H
     | [ |- _ ≈ _ ] => split; repeat intro

     | [ H : (_ ∧ _) _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- (_ ∧ _) _ ] => split

     | [ H : (_ ∨ _) _ |- _ ] =>
       let H1 := fresh "H" in inversion H as [H1|H1]; subst; clear H
     | [ H : ?P _ |- (?P ∨ _) _ ] => now left
     | [ H : ?P _ |- (_ ∨ ?P) _ ] => now right
     | [ H : ?P _ |- ((?P ∨ _) ∨ _) _ ] => now left; left
     | [ H : ?P _ |- ((_ ∨ ?P) ∨ _) _ ] => now left; right
     | [ H : ?P _ |- (_ ∨ (?P ∨ _)) _ ] => now right; left
     | [ H : ?P _ |- (_ ∨ (_ ∨ ?P)) _ ] => now right; right
     | [ H : ¬ ?P _ |- (¬ ?P ∨ _) _ ] => now left
     | [ H : ¬ ?P _ |- (_ ∨ ¬ ?P) _ ] => now right
     | [ H : ¬ ?P _ |- ((¬ ?P ∨ _) ∨ _) _ ] => now left; left
     | [ H : ¬ ?P _ |- ((_ ∨ ¬ ?P) ∨ _) _ ] => now left; right
     | [ H : ¬ ?P _ |- (_ ∨ (¬ ?P ∨ _)) _ ] => now right; left
     | [ H : ¬ ?P _ |- (_ ∨ (_ ∨ ¬ ?P)) _ ] => now right; right

     | [ H1 : ?P _, H2 : ?Q _ |- ((?P ∧ ?Q) ∨ _) _ ] => left
     | [ H1 : ?P _, H2 : ?Q _ |- (_ ∨ (?P ∧ ?Q)) _ ] => right

     | [ H : ¬ (_ ∨ _) _ |- _ ] => apply not_or in H
     | [ H : ¬ (_ ∧ _) _ |- _ ] => apply not_and in H

     | [ H : _ /\ _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- _ /\ _ ] => split

     | [ H : _ \/ _ |- _ ] =>
       let H1 := fresh "H" in inversion H as [H1|H1]; subst; clear H

     | [ H : (_ ↔ _) _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- (_ ↔ _) _ ] => split

     | [ |- _ -> _ ] => intro
     | [ H: ?P |- ?P ] => apply H

     | [ H : ?P ≈ ?Q |- _ ] => rewrite H in *; clear H

     | [ H : _ <-> _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- _ <-> _ ] => split

     | [ H1 : ?P, H2 : ~ ?P |- _ ] => contradiction
     | [ H1 : ?P _, H2 : ¬ ?P _ |- _ ] => contradiction

     | [ H : (⊥) _ |- _ ] => contradiction
     | [ H : ¬ (⊤) _ |- False ] => apply H

     | [ |- (⊤) _ ] => now constructor
     | [ |- ¬ _ _ ] => intro
     | [ |- (⊥) _ ] => elimtype False
     | [ |- ~ _ ] => intro
     | [ H : ¬ (fun _ => forall _, _) _ |- _ ] => unfold Complement, In in H

     | [ |- ◯ _ _ ] => unfold next

     | [ |- nat ] => exact 0

     | [ H : ~ (forall _, ~ _)        |- _ ] => apply not_all_not_ex in H
     | [ H : (forall _, ~ _) -> False |- _ ] => apply not_all_not_ex in H
     | [ H : ~ (forall _, _)          |- _ ] => apply not_all_ex_not in H
     | [ H : (forall _, _) -> False   |- _ ] => apply not_all_ex_not in H
     | [ H : ~ (exists _, ~ _)        |- _ ] => apply not_ex_not_all in H
     | [ H : (exists _, ~ _) -> False |- _ ] => apply not_ex_not_all in H
     | [ H : ~ (exists _, _)          |- _ ] => apply not_ex_all_not in H
     | [ H : (exists _, _) -> False   |- _ ] => apply not_ex_all_not in H

     | [ |- exists _, ¬ _ _ ] => apply not_all_ex_not; intro

     | [ H : forall i : nat, ?P (from i ?S) |- ?P ?S ] => apply (H 0)
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (tail ?S) ] => apply (H 1)
     | [ H : ?P ?S |- exists i : nat, ?P (from i ?S) ] => exists 0
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (from ?I (tail ?S)) ]
         => rewrite from_tail_S; apply H
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (tail (from ?I ?S)) ]
         => rewrite tail_from_S; apply H
     | [ H : ?P (tail ?S) |- exists i : nat, ?P (from i ?S) ] => exists 1
     | [ H : forall i : nat, ?P (from i (from ?X ?S))
       |- exists n : nat, ?P (from n (from _ ?S)) ] => eexists; rewrite from_from
     | [ H : forall i : nat, ?P (from i (tail ?S)) |- ?P (tail (from _ ?S)) ] =>
       rewrite tail_from
     | [ H : forall i : nat, ?P (tail (from i ?S)) |- ?P (from _ (tail ?S)) ] =>
       rewrite from_tail
     | [ H : forall i j : nat, ?P (from j (from i ?S)) |- ?P (from _ ?S) ] =>
       apply (H 0)
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (from ?I (from ?J ?S)) ] =>
       rewrite from_plus
     | [ H : ?P (from ?I (from ?J ?S)) |- exists i : nat, ?P (from i ?S) ] =>
       rewrite from_plus in H
     | [ H : ?P (from ?I ?S) |- exists i : nat, ?P (from i ?S) ] => exists I
     | [ H : ?P (from ?I ?S) |- exists i j : nat, ?P (from i (from j ?S)) ] =>
       exists I; exists 0
     | [ H : ?P (from ?I ?S) |- exists i j : nat, ?P (from j (from i ?S)) ] =>
       exists I; exists 0
     | [ H : ?P (tail (from ?I ?S)) |- exists i : nat, ?P (from i (tail ?S)) ] =>
       exists I; rewrite from_tail
     | [ H : ?P (from ?I (tail ?S)) |- exists i : nat, ?P (tail (from i ?S)) ] =>
       exists I; rewrite tail_from

     end;
     unfold In, next, until, any, every, release, weakUntil in *;
     intros;
     try rewrite !Complement_Complement in *;
     try unshelve intuition eauto;
     try unshelve firstorder eauto;
     try unshelve eauto;
     try (now left);
     try (now right);
     try (now left; left);
     try (now left; right);
     try (now right; left);
     try (now right; right)).


Lemma not_swap (φ ψ : LTL) : (¬ φ ≈ ψ) <-> (φ ≈ ¬ ψ).
Proof.
  split; intro.
  - now rewrite <- H, Complement_Complement.
  - now rewrite H, Complement_Complement.
Qed.

(***********************************************************************
 *
 * The properties below follow the presentation in the paper
 *
 *   "A Calculational Deductive System for Linear Temporal Logic"
 *
 * by Warford, Vega and Staley, https://dl.acm.org/doi/10.1145/3387109
 *)

(*** 3.1 Next *)

Theorem (* 1 *) next_self_dual (φ : LTL) : ◯¬ φ ≈ ¬◯ φ.
Proof. now solve. Qed.

Theorem (* 2 *) next_distr_impl (φ ψ : LTL) : ◯ (φ → ψ) ≈ ◯ φ → ◯ ψ.
Proof. now solve. Qed.

Corollary (* 3 *) next_linearity (φ : LTL) : ◯ φ ≈ ¬◯¬ φ.
Proof. now rewrite next_self_dual; apply not_swap. Qed.

Lemma (* 4 *) next_distr_or (φ ψ : LTL) : ◯ (φ ∨ ψ) ≈ ◯ φ ∨ ◯ ψ.
Proof. now solve. Qed.

Lemma (* 5 *) next_distr_and (φ ψ : LTL) : ◯ (φ ∧ ψ) ≈ ◯ φ ∧ ◯ ψ.
Proof. now solve. Qed.

Lemma (* 6 *) next_distr_next_eq (φ ψ : LTL) : ◯ (φ ↔ ψ) ≈ ◯ φ ↔ ◯ ψ.
Proof. now solve. Qed.

Lemma (* 7 *) next_top : ◯ (⊤) ≈ ⊤.
Proof. now solve. Qed.

Lemma (* 8 *) next_bottom : ◯ (⊥) ≈ ⊥.
Proof. now solve. Qed.


(************************************************************************)

Lemma law_1 : ¬(⊤) ≈ ⊥.
Proof. now solve. Qed.
Lemma law_2 : ¬(⊥) ≈ ⊤.
Proof. now solve. Qed.
Lemma law_3 (φ : LTL) : ¬¬ φ ≈ φ.
Proof. now solve. Qed.
Lemma law_4 (φ ψ : LTL) : (φ ≈ ψ) -> ¬ φ ≈ ¬ ψ.
Proof. intro; now rewrite H. Qed.
Lemma law_5 (φ ψ χ : LTL) : φ ∨ (ψ ∨ χ) ≈ (φ ∨ ψ) ∨ χ.
Proof. now solve. Qed.
Lemma law_6 (φ ψ : LTL) : φ ∨ ψ ≈ ψ ∨ φ.
Proof. now solve. Qed.
Lemma law_7 (φ : LTL) : φ ∨ (⊥) ≈ φ.
Proof. now solve. Qed.
Lemma law_8 (φ ψ : LTL) : φ ∧ ψ ≈ ψ ∧ φ.
Proof. now solve. Qed.
Lemma law_9 (φ ψ χ : LTL) : φ ∧ (ψ ∧ χ) ≈ (φ ∧ ψ) ∧ χ.
Proof. now solve. Qed.
Lemma law_10 (φ : LTL) : φ ∧ (⊤) ≈ φ.
Proof. now solve. Qed.
Lemma law_11 (φ ψ χ : LTL) : φ ∨ (ψ ∧ χ) ≈ (φ ∨ ψ) ∧ (φ ∨ χ).
Proof. now solve. Qed.
Lemma law_12 (φ ψ χ : LTL) : φ ∧ (ψ ∨ χ) ≈ (φ ∧ ψ) ∨ (φ ∧ χ).
Proof. now solve. Qed.
Lemma law_13 (φ ψ : LTL) : ¬(φ ∨ ψ) ≈ ¬ φ ∧ ¬ ψ.
Proof. now solve. Qed.
Lemma law_14 (φ ψ : LTL) : ¬(φ ∧ ψ) ≈ ¬ φ ∨ ¬ ψ.
Proof. now solve. Qed.

Lemma law_18 : ◇ (⊤) ≈ ⊤.
Proof. solve; now exists 0; constructor. Qed.
Lemma law_19 : ◇ (⊥) ≈ ⊥.
Proof. now solve. Qed.
Lemma law_20 : □ (⊤) ≈ ⊤.
Proof. now solve. Qed.
Lemma law_21 : □ (⊥) ≈ ⊥.
Proof. now solve. Qed.
Lemma law_23 (φ : LTL) : ¬□ φ ≈ ◇¬ φ.
Proof. now solve. Qed.
Lemma law_24 (φ : LTL) : ¬◇ φ ≈ □¬ φ.
Proof. now solve. Qed.
Lemma law_25 (φ : LTL) : ¬◇□ φ ≈ □◇¬ φ.
Proof. now solve. Qed.
Lemma law_26 (φ : LTL) : ¬□◇ φ ≈ ◇□¬ φ.
Proof. now solve. Qed.
Lemma law_27 (φ : LTL) : forall s, □ φ s -> φ s.
Proof. now solve. Qed.
Lemma law_28 (φ : LTL) : forall s, φ s -> ◇ φ s.
Proof. now solve. Qed.
Lemma law_29 (φ : LTL) : forall s, □ φ s -> ◯ φ s.
Proof. now solve. Qed.
Lemma law_30 (φ : LTL) : forall s, □ φ s -> ◯□ φ s.
Proof. now solve. Qed.
Lemma law_31 (φ : LTL) : forall s, □ φ s -> □◯ φ s.
Proof. now solve. Qed.
Lemma law_32 (φ : LTL) : forall s, ◯ φ s -> ◇ φ s.
Proof. now solve. Qed.
Lemma law_33 (φ : LTL) : forall s, □ φ s -> ◇ φ s.
Proof. now solve. Qed.
Lemma law_34 (φ : LTL) : forall s, ◇□ φ s -> □◇ φ s.
Proof. now solve. Qed.
Lemma law_35 (φ : LTL) : forall s, □¬ φ s -> ¬□ φ s.
Proof. now solve. Qed.

Lemma law_36 (φ : LTL) : □□ φ ≈ □ φ.
Proof. now solve. Qed.
Lemma law_37 (φ : LTL) : ◇◇ φ ≈ ◇ φ.
Proof. now solve. Qed.
Lemma law_38 (φ : LTL) : □◯ φ ≈ ◯□ φ.
Proof. now solve. Qed.
Lemma law_39 (φ : LTL) : ◇◯ φ ≈ ◯◇ φ.
Proof. now solve. Qed.
Lemma law_40 (φ : LTL) : □ φ ≈ φ ∧ ◯□ φ.
Proof.
  solve.
  generalize dependent x.
  induction i; auto; simpl.
  now intros; intuition.
Qed.
Lemma law_41 (φ : LTL) : □ φ ≈ φ ∧ ◯ φ ∧ ◯□ φ.
Proof.
  solve.
  generalize dependent x.
  induction i; auto; simpl.
  now intros; intuition.
Qed.
Lemma law_42 (φ : LTL) : ◇ φ ≈ φ ∨ ◯◇ φ.
Proof.
  solve.
  - generalize dependent x.
    induction x0; auto; intros; simpl.
    + now left.
    + right; unfold In.
      exists x0.
      now rewrite from_tail_S.
  - exists (S x0).
    now rewrite <- from_tail_S.
Qed.
Lemma law_43 (φ : LTL) : ◇□◇ φ ≈ □◇ φ.
Proof.
  solve.
  - destruct (H i).
    exists (x1 + x0).
    rewrite from_from in H0.
    rewrite (from_plus _ x1 x0) in H0.
    now rewrite from_from in H0.
  - exists 0; intros; simpl.
    now apply H.
Qed.
Lemma law_44 (φ : LTL) : □◇□ φ ≈ ◇□ φ.
Proof.
  solve.
  - now apply (H 0).
  - exists x0; simpl.
    intros.
    specialize (H (i0 + i)); simpl in H.
    setoid_rewrite from_from at 2.
    now rewrite <- from_plus in H.
Qed.
Lemma law_45 (φ : LTL) : □◇□◇ φ ≈ □◇ φ.
Proof. now rewrite law_44, law_43. Qed.
Lemma law_46 (φ : LTL) : ◇□◇□ φ ≈ ◇□ φ.
Proof. now rewrite law_44, law_37. Qed.
Lemma law_47 (φ : LTL) : ◯□◇ φ ≈ □◇ φ.
Proof. Fail now solve. Abort.
Lemma law_48 (φ : LTL) : ◯◇□ φ ≈ ◇□ φ.
Proof. Fail now solve. Abort.

Lemma law_53 (φ ψ : LTL) : □ (φ ∧ ψ) ≈ □ φ ∧ □ ψ.
Proof.
  solve;
  specialize (H i);
  now solve.
Qed.
Lemma law_54 (φ ψ : LTL) : □ (φ ∨ ψ) ≉ □ φ ∨ □ ψ.
Proof. Fail now solve. Abort.   (* appears unsolvable *)
Lemma law_55 (φ : LTL) : φ ∨ ◇ φ ≈ ◇ φ.
Proof.
  solve.
  - now right; exists x0.
Qed.
Lemma law_56 (φ : LTL) : ◇ φ ∧ φ ≈ φ.
Proof. now solve. Qed.
Lemma law_57 (φ ψ : LTL) : ◇ (φ ∧ ψ) ≉ ◇ φ ∧ ◇ ψ.
Proof. Fail now solve. Abort.   (* appears unsolvable *)
Lemma law_58 (φ ψ : LTL) : ◇ (φ ∨ ψ) ≉ ◇ φ ∨ ◇ ψ.
Proof. Fail now solve. Abort.   (* appears unsolvable *)
Lemma law_59 (φ : LTL) : φ ∧ □ φ ≈ □ φ.
Proof. now solve. Qed.
Lemma law_60 (φ : LTL) : □ φ ∨ φ ≈ φ.
Proof. now solve. Qed.
Lemma law_61 (φ : LTL) : ◇ φ ∧ □ φ ≈ □ φ.
Proof. now solve. Qed.
Lemma law_62 (φ : LTL) : □ φ ∨ ◇ φ ≈ ◇ φ.
Proof.
  solve.
  now right; exists x0.
Qed.
Lemma law_63 (φ ψ : LTL) : ◇□ (φ ∧ ψ) ≈ ◇□ φ ∧ ◇□ ψ.
Proof.
  solve.
  - exists x0; intros.
    now destruct (H i).
  - exists x0; intros.
    now destruct (H i).
  - admit.
Abort.
Lemma law_64 (φ ψ : LTL) : □◇ (φ ∨ ψ) ≈ □◇ φ ∨ □◇ ψ.
Proof. solve. Abort.
Lemma law_65 (φ ψ : LTL) : ◇□ (φ → □ ψ) ≈ ◇□¬ φ ∧ ◇□ ψ.
Proof.
  solve.
  - exists x0; intros.
    specialize (H i); solve.
    admit.
  - exists x0; intros.
    specialize (H i); solve.
    admit.
  - admit.
Abort.
Lemma law_66 (φ ψ : LTL) : □ (□◇ φ → ◇ ψ) ≈ ◇□¬ φ ∧ □◇ ψ.
Proof. Fail now solve. Abort.
Lemma law_67 (φ ψ : LTL) : □ ((φ ∨ □ ψ) ∧ (□ φ ∨ ψ)) ≈ □ φ ∨ □ ψ.
Proof. Fail now solve. Abort.
Lemma law_68 (φ : LTL) : ◇ φ ≈ ¬□¬ φ.
Proof. now solve. Qed.
Lemma law_69 (φ : LTL) : □ φ ≈ ¬◇¬ φ.
Proof.
  solve.
  specialize (H i); simpl in H.
  unfold Complement, In, not in H.
  now apply NNPP in H.
Qed.
Lemma law_70 (φ : LTL) : ◇ φ ∧ □¬ φ ≈ ⊥.
Proof. now solve. Qed.
Lemma law_71 (φ : LTL) : □ φ ∧ ◇¬ φ ≈ ⊥.
Proof. now solve. Qed.
Lemma law_72 (φ : LTL) : □ φ ∧ □¬ φ ≈ ⊥.
Proof. now solve. Qed.
Lemma law_73 (φ : LTL) : □◇ φ ∧ ◇□¬ φ ≈ ⊥.
Proof. now solve. Qed.
Lemma law_74 (φ : LTL) : ◇□ φ ∧ □◇¬ φ ≈ ⊥.
Proof. now solve. Qed.
Lemma law_75 (φ : LTL) : ◇□ φ ∧ ◇□¬ φ ≈ ⊥.
Proof. Fail now solve. Abort.
Lemma law_76 (φ : LTL) : forall s, (◇ φ ∨ □¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_77 (φ : LTL) : forall s, (□ φ ∨ ◇¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_78 (φ : LTL) : forall s, (◇ φ ∨ ◇¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_79 (φ : LTL) : forall s, (□◇ φ ∨ ◇□¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_80 (φ : LTL) : forall s, (□◇ φ ∨ □◇¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_81 (φ : LTL) : forall s, (◇□ φ ∨ □◇¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_82 (φ ψ : LTL) : forall s, ◇ (φ → ψ) s -> (□ φ → ◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_83 (φ : LTL) : forall s, (φ → □ φ) s -> (φ → ◯□ φ) s.
Proof. Fail now solve. Abort.
Lemma law_84 (φ : LTL) : forall s, (φ ∧ ◇¬ φ) s -> (◇ (φ ∧ ◯¬ φ)) s.
Proof. Fail now solve. Abort.
Lemma law_85 (φ ψ : LTL) : forall s, □ (φ → ψ) s -> (□ φ → □ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_86 (φ ψ : LTL) : forall s, (□ φ ∨ □ ψ) s -> □ (φ ∨ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_87 (φ ψ : LTL) : forall s, (□ φ ∧ ◇ ψ) s -> ◇ (φ ∧ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_88 (φ ψ : LTL) : forall s, (◇ φ → ◇ ψ) s -> ◇ (φ → ψ) s.
Proof. Fail now solve. Abort.
Lemma law_89 (φ ψ : LTL) : forall s, ◇ (φ ∧ ψ) s -> (◇ φ ∧ ◇ ψ) s.
Proof. now solve. Qed.
Lemma law_90 (φ ψ : LTL) : forall s, □◇ (φ ∧ ψ) s -> (□◇ φ ∧ □◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_91 (φ ψ : LTL) : forall s, □◇ (φ ∨ ψ) s -> (□◇ φ ∨ □◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_92 (φ ψ : LTL) : forall s, ◇□ (φ ∧ ψ) s -> (◇□ φ ∧ ◇□ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_93 (φ ψ : LTL) : forall s, (◇□ φ ∨ ◇□ ψ) s -> ◇□ (φ ∨ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_94 (φ ψ : LTL) : forall s, (◇□ φ ∧ □◇ ψ) s -> □◇ (φ ∧ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_95 (φ ψ : LTL) : forall s, (◇□ φ ∧ □ (□ φ → ◇ ψ)) s -> ◇ ψ s.
Proof. Fail now solve. Abort.
Lemma law_96 (φ ψ : LTL) : forall s, □ (φ → ψ) s -> (◯ φ → ◯ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_97 (φ ψ : LTL) : forall s, □ (φ → ψ) s -> (◇ φ → ◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_98 (φ ψ : LTL) : forall s, □ (φ → ψ) s -> (□◇ φ → □◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_99 (φ ψ : LTL) : forall s, □ (φ → ψ) s -> (◇□ φ → ◇□ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_100 (φ ψ : LTL) : forall s, □ φ s -> (◯ ψ → ◯ (φ ∧ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_101 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ → ◇ (φ ∧ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_102 (φ ψ : LTL) : forall s, □ φ s -> (□ ψ → □ (φ ∧ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_103 (φ ψ : LTL) : forall s, □ φ s -> (◯ ψ → ◯ (φ ∨ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_104 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ → ◇ (φ ∨ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_105 (φ ψ : LTL) : forall s, □ φ s -> (□ ψ → □ (φ ∨ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_106 (φ ψ : LTL) : forall s, □ φ s -> (◯ ψ → ◯ (φ → ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_107 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ → ◇ (φ → ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_108 (φ ψ : LTL) : forall s, □ φ s -> (□ ψ → □ (φ → ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_109 (φ ψ : LTL) : forall s, □ (□ φ → ψ) s -> (□ φ → □ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_110 (φ ψ : LTL) : forall s, □ (φ → ◇ψ) s -> (◇ φ → ◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_111 (φ : LTL) : forall s, □ (φ → ◯ φ) s -> (φ → □ φ) s.
Proof. Fail now solve. Abort.
Lemma law_112 (φ ψ : LTL) : forall s, □ (φ → ◯ ψ) s -> (φ → ◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_113 (φ : LTL) : forall s, □ (φ → ◯¬ φ) s -> (φ → ¬□ φ) s.
Proof. Fail now solve. Abort.
Lemma law_114 (φ : LTL) : forall s, □ (◯ φ → φ) s -> (◇ φ → φ) s.
Proof. Fail now solve. Abort.
Lemma law_115 (φ ψ : LTL) : forall s, □ (φ ∨ ◯ ψ → ψ) s -> (◇ φ → ψ) s.
Proof. Fail now solve. Abort.
Lemma law_116 (φ ψ : LTL) : forall s, □ (φ → ◯ φ ∧ ψ) s -> (φ → □ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_117 (φ ψ χ : LTL) : forall s, □ (φ → (◯ φ ∧ ψ) ∨ χ) s -> (φ → □ ψ ∨ (ψ U χ)) s.
Proof. Fail now solve. Abort.
Lemma law_118 (φ ψ : LTL) : forall s, □ (φ → ◯ (φ ∨ ψ)) s -> (φ → □ φ ∨ (φ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_119 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ψ) ∧ (ψ → ◯ χ) ∧ (χ → ρ)) s -> (φ → ◯ ρ) s.
Proof. Fail now solve. Abort.
Lemma law_120 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ψ) ∧ (ψ → ◇ χ) ∧ (χ → ρ)) s -> (φ → ◇ ρ) s.
Proof. Fail now solve. Abort.
Lemma law_121 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ψ) ∧ (ψ → □ χ) ∧ (χ → ρ)) s -> (φ → □ ρ) s.
Proof. Fail now solve. Abort.
Lemma law_122 (φ ψ χ : LTL) : forall s, □ ((φ → ◇ ψ) ∧ (ψ → ◇ χ)) s -> (φ → ◇ χ) s.
Proof. Fail now solve. Abort.
Lemma law_123 (φ ψ χ : LTL) : forall s, □ ((φ → □ ψ) ∧ (ψ → □ χ)) s -> (φ → □ χ) s.
Proof. Fail now solve. Abort.
Lemma law_124 (φ ψ χ : LTL) : forall s, (□ (□ φ → ◇ ψ) ∧ (ψ → ◯ χ)) s -> (□ φ → ◯□◇ χ) s.
Proof. Fail now solve. Abort.
Lemma law_125 (φ ψ : LTL) : forall s, □ (φ ∨ ψ) s -> exists u, □ ((φ ∧ u) ∨ (ψ ∧ ¬ u)) s.
Proof. Fail now solve. Abort.
Lemma law_126 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ◇ (ψ ∨ χ)) ∧ (ψ → ◇ ρ) ∧ (χ → ◇ ρ)) s -> (φ → ◇ ρ) s.
Proof. Fail now solve. Abort.
Lemma law_127 (φ ψ : LTL) : forall s, (□ (□ φ → ψ) ∨ □ (□ ψ → φ)) s.
Proof. Fail now solve. Abort.
Lemma law_128 (φ : LTL) : φ U (⊥) ≈ ⊥.
Proof. now solve. Qed.
Lemma law_129 (φ : LTL) : .
Proof. Fail now solve. Abort.
Lemma law_130 (φ : LTL) : .
Proof. Fail now solve. Abort.
Lemma law_131 (φ : LTL) : .
Proof. Fail now solve. Abort.
Lemma law_132 (φ : LTL) : ¬ φ U φ ≈ ◇ φ.
Proof. Fail now solve. Abort.
Lemma law_133 (φ ψ : LTL) : forall s, ψ s -> (φ U φ) s.
Proof. Fail now solve. Abort.
Lemma law_134 (φ ψ : LTL) : forall s, (φ U ψ) s -> (φ ∨ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_135 (φ ψ : LTL) : forall s, (φ ∧ ψ) s -> (φ U ψ) s.
Proof. Fail now solve. Abort.
Lemma law_136 (φ ψ : LTL) : forall s, ((φ U ψ) ∨ (φ U ¬ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_137 (φ ψ : LTL) : φ ∨ (φ U ψ) ≈ φ ∨ ψ.
Proof. Fail now solve. Abort.
Lemma law_138 (φ ψ : LTL) : (φ U ψ) ∨ ψ ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_139 (φ ψ : LTL) : (φ U ψ) ∧ ψ ≈ ψ.
Proof. Fail now solve. Abort.
Lemma law_140 (φ ψ : LTL) : (φ U ψ) ∨ (φ ∧ ψ) ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_141 (φ ψ : LTL) : (φ U ψ) ∧ (φ ∨ ψ) ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_142 (φ ψ : LTL) : φ U (φ U ψ) ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_143 (φ ψ : LTL) : (φ U ψ) U ψ ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_144 (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ ◯ (φ U ψ)).
Proof. Fail now solve. Abort.
Lemma law_145 (φ ψ : LTL) : φ U ψ ≈ (φ ∨ ψ) U ψ.
Proof. Fail now solve. Abort.
Lemma law_146 (φ ψ : LTL) : φ U ψ ≈ (φ ∧ ¬ ψ) U ψ.
Proof. Fail now solve. Abort.
Lemma law_147 (φ ψ χ : LTL) : φ U (ψ ∨ χ) ≈ (φ U ψ) ∨ (φ U χ).
Proof. Fail now solve. Abort.
Lemma law_148 (φ ψ χ : LTL) : forall s, ((φ U χ) ∨ (ψ U χ)) s -> ((φ ∨ ψ) U χ) s.
Proof. now solve. Qed.
Lemma law_149 (φ ψ χ : LTL) : (φ ∧ ψ) U χ ≈ (φ U χ) ∧ (ψ U χ).
Proof. Fail now solve. Abort.
Lemma law_150 (φ ψ χ : LTL) : forall s, (φ U (ψ ∧ χ)) s -> ((φ U ψ) ∧ (φ U χ)) s.
Proof. now solve. Qed.
Lemma law_151 (φ ψ χ : LTL) : forall s, (φ U (ψ ∧ χ)) s -> (φ U (ψ U χ)) s.
Proof. Fail now solve. Abort.
Lemma law_152 (φ ψ χ : LTL) : forall s, ((φ ∧ ψ) U χ) s -> ((φ U ψ) U χ) s.
Proof. Fail now solve. Abort.
Lemma law_153 (φ ψ χ : LTL) : forall s, ((φ ∧ ψ) U χ) s -> (φ U (ψ U χ)) s.
Proof. Fail now solve. Abort.
Lemma law_154 (φ ψ : LTL) : ◯ (φ U ψ) ≈ (◯ φ) U (◯ ψ).
Proof. Fail now solve. Abort.
Lemma law_155 (φ ψ : LTL) : ◇ (φ U ψ) ≉ (◇ φ) U (◇ ψ).
Proof. Fail now solve. Abort.
Lemma law_156 (φ : LTL) : ◇ φ ≈ ⊤ U φ.
Proof. Fail now solve. Abort.
Lemma law_157 (φ ψ : LTL) : (φ U ψ) ∧ ◇ ψ ≈ φ U ψ.
Proof. now solve. Qed.
Lemma law_158 (φ ψ : LTL) : (φ U ψ) ∨ ◇ ψ ≈ ◇ ψ.
Proof. Fail now solve. Abort.
Lemma law_159 (φ ψ : LTL) : φ U ◇ ψ ≈ ◇ ψ.
Proof. Fail now solve. Abort.
Lemma law_160 (φ : LTL) : φ U □ φ ≈ □ φ.
Proof. Fail now solve. Abort.
Lemma law_161 (φ ψ : LTL) : φ U □ ψ ≈ □ (φ U ψ).
Proof. Fail now solve. Abort.
Lemma law_162 (φ ψ : LTL) : forall s, (◇ φ → ((φ → ψ) U φ)) s.
Proof. Fail now solve. Abort.
Lemma law_163 (φ ψ χ : LTL) : forall s, ((φ U ψ) ∧ (¬ ψ U χ)) s -> (φ U χ) s.
Proof. Fail now solve. Abort.
Lemma law_164 (φ ψ χ : LTL) : forall s, (φ U (ψ U χ)) s -> ((φ ∨ ψ) U χ) s.
Proof. Fail now solve. Abort.
Lemma law_165 (φ ψ χ : LTL) : forall s, ((φ → ψ) U χ) s -> ((φ U χ) → (ψ U χ)) s.
Proof. Fail now solve. Abort.
Lemma law_166 (φ ψ χ : LTL) : forall s, ((¬ φ U (ψ U χ)) ∧ (φ U χ)) s -> (ψ U χ) s.
Proof. Fail now solve. Abort.
Lemma law_167 (φ ψ χ : LTL) : forall s, ((φ U (¬ ψ U χ)) ∧ (ψ U χ)) s -> (φ U χ) s.
Proof. Fail now solve. Abort.
Lemma law_168 (φ ψ : LTL) : forall s, ((φ U ψ) ∧ (¬ ψ U φ)) s -> φ s.
Proof. Fail now solve. Abort.
Lemma law_169 (φ ψ : LTL) : forall s, (φ ∧ (¬ φ U ψ)) s -> ψ s.
Proof. Fail now solve. Abort.
Lemma law_170 (φ ψ : LTL) : forall s, □ φ s -> (◯ ψ → ◯ (φ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_171 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ → ◇ (φ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_172 (φ ψ : LTL) : forall s, □ φ s -> (□ ψ → □ (φ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_173 (φ ψ : LTL) : forall s, □ φ s -> ¬(ψ U ¬ φ) s.
Proof. now solve. Qed.
Lemma law_174 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ) s -> (φ U ψ) s.
Proof. now solve. Qed.
Lemma law_175 (φ ψ χ : LTL) : forall s, (□ φ ∧ (ψ U χ)) s -> ((φ ∧ ψ) U (φ ∧ χ)) s.
Proof. Fail now solve. Abort.
Lemma law_176 (φ ψ χ : LTL) : forall s, □ (φ → ψ) s -> ((χ U φ) → (χ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_177 (φ ψ χ : LTL) : forall s, □ (φ → ψ) s -> ((φ U χ) → (ψ U χ)) s.
Proof. Fail now solve. Abort.
Lemma law_178 (φ ψ : LTL) : forall s, (φ U ψ) s -> (◇ ψ) s.
Proof. now solve. Qed.
Lemma law_179 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ψ U χ) ∧ (χ → ψ U ρ)) s -> (φ → □ χ) s.
Proof. Fail now solve. Abort.
Lemma law_180 (φ ψ χ ρ : LTL) : forall s, □ ((φ → χ) ∧ (ψ → ρ)) s -> (φ U ψ → χ U ρ) s.
Proof. Fail now solve. Abort.
Lemma law_181 (φ ψ χ : LTL) : forall s, □ (φ → ¬ ψ ∧ ◯ χ) s -> (φ → ¬(ψ U χ)) s.
Proof. Fail now solve. Abort.

Lemma law_182 (φ : LTL) : φ W φ ≈ φ.
Proof. Fail now solve. Abort.
Lemma law_183 (φ ψ : LTL) : φ W ψ ≈ (φ U ψ) ∨ □ φ.
Proof. now solve. Qed.
Lemma law_184 (φ ψ : LTL) : ¬(φ W ψ) ≈ ¬ ψ U (¬ φ ∧ ¬ ψ).
Proof. Fail now solve. Abort.
Lemma law_185 (φ ψ : LTL) : ¬(φ W ψ) ≈ (φ ∧ ¬ ψ) U (¬ φ ∧ ¬ ψ).
Proof. Fail now solve. Abort.
Lemma law_186 (φ ψ : LTL) : ¬(φ U ψ) ≈ ¬ ψ W (¬ φ ∧ ¬ ψ).
Proof. Fail now solve. Abort.
Lemma law_187 (φ ψ : LTL) : ¬(φ U ψ) ≈ (φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ).
Proof. Fail now solve. Abort.
Lemma law_188 (φ ψ : LTL) : ¬(¬ φ U ¬ ψ) ≈ ψ W (φ ∧ ψ).
Proof. Fail now solve. Abort.
Lemma law_189 (φ ψ : LTL) : ¬(¬ φ U ¬ ψ) ≈ (¬ φ ∧ ψ) W (φ ∧ ψ).
Proof. Fail now solve. Abort.
Lemma law_190 (φ ψ : LTL) : ¬(¬ φ W ¬ ψ) ≈ ψ U (φ ∧ ψ).
Proof. Fail now solve. Abort.
Lemma law_191 (φ ψ : LTL) : ¬(¬ φ W ¬ ψ) ≈ (¬ φ ∧ ψ) U (φ ∧ ψ).
Proof. Fail now solve. Abort.
Lemma law_192 (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Proof. Fail now solve. Abort.
Lemma law_193 (φ ψ : LTL) : φ W ψ ≈ (φ ∨ ψ) W ψ.
Proof. Fail now solve. Abort.
Lemma law_194 (φ ψ : LTL) : φ W ψ ≈ □ (φ ∧ ¬ ψ) ∨ (φ U ψ).
Proof. Fail now solve. Abort.
Lemma law_195 (φ ψ : LTL) : φ U ψ ≈ (φ W ψ) ∧ ◇ ψ.
Proof. Fail now solve. Abort.
Lemma law_196 (φ ψ : LTL) : φ U ψ ≈ (φ W ψ) ∧ ¬□¬ ψ.
Proof. Fail now solve. Abort.
Lemma law_197 (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof. Fail now solve. Abort.
Lemma law_198 (φ ψ : LTL) : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).
Proof. Fail now solve. Abort.
Lemma law_199 (φ ψ : LTL) : φ W ψ ≈ (φ ∧ ¬ ψ) W ψ.
Proof. Fail now solve. Abort.
Lemma law_200 (φ ψ : LTL) : φ W (φ W ψ) ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_201 (φ ψ : LTL) : (φ W ψ) W ψ ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_202 (φ ψ : LTL) : φ W (φ U ψ) ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_203 (φ ψ : LTL) : (φ U ψ) W ψ ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_204 (φ ψ : LTL) : φ U (φ W ψ) ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_205 (φ ψ : LTL) : (φ W ψ) U ψ ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_206 (φ ψ : LTL) : ◯ (φ W ψ) ≈ ◯ φ W ◯ ψ.
Proof. Fail now solve. Abort.
Lemma law_207 (φ ψ : LTL) : φ W ◇ ψ ≈ □ φ ∨ ◇ ψ.
Proof. Fail now solve. Abort.
Lemma law_208 (φ : LTL) : ◇ φ W φ ≈ ◇ φ.
Proof. Fail now solve. Abort.
Lemma law_209 (φ ψ : LTL) : □ φ ∧ (φ W ψ) ≈ □ φ.
Proof. now solve. Qed.
Lemma law_210 (φ ψ : LTL) : □ φ ∨ (φ W ψ) ≈ φ W ψ.
Proof. now solve. Qed.
Lemma law_211 (φ : LTL) : φ W □ φ ≈ □ φ.
Proof. Fail now solve. Abort.
Lemma law_212 (φ : LTL) : □ φ ≈ φ W ⊥.
Proof. now solve. Qed.
Lemma law_213 (φ : LTL) : ◇ φ ≈ ¬(¬ φ W ⊥).
Proof. now solve. Qed.
Lemma law_214 (φ : LTL) : ⊤ W φ ≈ ⊤.
Proof. now solve. Qed.
Lemma law_215 (φ : LTL) : φ W (⊤) ≈ ⊤.
Proof. Fail now solve. Abort.
Lemma law_216 (φ : LTL) : ⊥ W φ ≈ φ.
Proof. Fail now solve. Abort.
Lemma law_217 (φ ψ χ : LTL) : φ W (ψ ∨ χ) ≈ (φ W ψ) ∨ (φ W χ).
Proof. Fail now solve. Abort.
Lemma law_218 (φ ψ χ : LTL) : (φ ∧ ψ) W χ ≈ (φ W χ) ∧ (ψ W χ).
Proof. Fail now solve. Abort.
Lemma law_219 (φ ψ : LTL) : φ ∨ (φ W ψ) ≈ φ ∨ ψ.
Proof. Fail now solve. Abort.
Lemma law_220 (φ ψ : LTL) : (φ W ψ) ∨ ψ ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_221 (φ ψ : LTL) : (φ W ψ) ∧ ψ ≈ ψ.
Proof. Fail now solve. Abort.
Lemma law_222 (φ ψ : LTL) : (φ W ψ) ∧ (φ ∨ ψ) ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_223 (φ ψ : LTL) : (φ W ψ) ∨ (φ ∧ ψ) ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_224 (φ ψ : LTL) : ((¬ φ U ψ) ∨ (¬ ψ U φ)) ≈ ◇ (φ ∨ ψ).
Proof. Fail now solve. Abort.
Lemma law_225 (φ ψ : LTL) : forall s, ψ s -> (φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_226 (φ ψ : LTL) : forall s, (φ W φ) s -> (φ ∨ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_227 (φ ψ : LTL) : forall s, (φ W φ) s -> (□ φ ∨ ◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_228 (φ : LTL) : forall s, (¬ φ W φ) s.
Proof. Fail now solve. Abort.
Lemma law_229 (φ ψ : LTL) : forall s, ((φ → ψ) W φ) s.
Proof. Fail now solve. Abort.
Lemma law_230 (φ ψ : LTL) : forall s, ((φ W ψ) ∨ (φ W ¬ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_231 (φ ψ χ : LTL) : forall s, (φ W (ψ ∧ χ)) s -> ((φ W ψ) ∧ (φ W χ)) s.
Proof. Fail now solve. Abort.
Lemma law_232 (φ ψ χ : LTL) : forall s, ((φ W χ) ∨ (ψ W χ)) s -> ((φ ∨ ψ) W χ) s.
Proof. Fail now solve. Abort.
Lemma law_233 (φ ψ : LTL) : forall s, (φ U ψ) s -> (φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_234 (φ ψ : LTL) : forall s, (φ W □ ψ) s -> □ (φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_235 (φ ψ : LTL) : forall s, ¬(φ U ψ) s -> ((φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_236 (φ ψ : LTL) : forall s, ¬(φ W ψ) s -> ((φ ∧ ¬ ψ) U (¬ φ ∧ ¬ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_237 (φ ψ χ : LTL) : forall s, ((φ → ψ) W χ) s -> ((φ W χ) → (ψ W χ)) s.
Proof. Fail now solve. Abort.
Lemma law_238 (φ ψ : LTL) : forall s, □ φ s -> (φ W ψ) s.
Proof. now solve. Qed.
Lemma law_239 (φ ψ : LTL) : forall s, □ φ s -> (◯ ψ → ◯ (φ W ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_240 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ → ◇ (φ W ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_241 (φ ψ : LTL) : forall s, □ φ s -> (□ ψ → □ (φ W ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_242 (φ ψ : LTL) : forall s, □ (φ ∨ ψ) s -> (φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_243 (φ ψ : LTL) : forall s, □ (¬ ψ → φ) s -> (φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_244 (φ ψ χ : LTL) : forall s, □ (φ → (◯ φ ∧ ψ) ∨ χ) s -> (φ → ψ W χ) s.
Proof. Fail now solve. Abort.
Lemma law_245 (φ ψ : LTL) : forall s, □ (φ → ◯ (φ ∨ ψ)) s -> (φ → φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_246 (φ ψ : LTL) : forall s, □ (φ → ◯ φ) s -> (φ → φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_247 (φ ψ : LTL) : forall s, □ (φ → ψ ∧ ◯ φ) s -> (φ → φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_248 (φ ψ χ : LTL) : forall s, (□ φ ∧ (ψ W χ)) s -> ((φ ∧ ψ) W (φ ∧ χ)) s.
Proof. Fail now solve. Abort.
Lemma law_249 (φ ψ : LTL) : forall s, ((φ W ψ) ∧ □¬ ψ) s -> □ φ s.
Proof. now solve. Qed.
Lemma law_250 (φ ψ : LTL) : forall s, □ φ s -> ((φ U ψ) ∨ □¬ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_251 (φ ψ : LTL) : forall s, (¬□ φ ∧ (φ W ψ)) s -> ◇ ψ s.
Proof. now solve. Qed.
Lemma law_252 (φ ψ : LTL) : forall s, ◇ ψ s -> (¬□ φ ∨ (φ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_253 (φ ψ χ : LTL) : forall s, □ (φ → ψ) s -> (φ W χ → ψ W χ) s.
Proof. Fail now solve. Abort.
Lemma law_254 (φ ψ χ : LTL) : forall s, □ (φ → ψ) s -> (χ W φ → χ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_255 (φ ψ χ ρ : LTL) : forall s, □ ((φ → χ) ∧ (ψ → ρ)) s -> ((φ W ψ) → (χ W ρ)) s.
Proof. Fail now solve. Abort.
Lemma law_256 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ψ W χ) ∧ (χ → ψ W ρ)) s -> (φ → ψ W ρ) s.
Proof. Fail now solve. Abort.
Lemma law_257 (φ ψ χ : LTL) : forall s, ((φ U ψ) W χ) s -> ((φ W ψ) W χ) s.
Proof. Fail now solve. Abort.
Lemma law_258 (φ ψ χ : LTL) : forall s, (φ W (ψ U χ)) s -> (φ W (ψ W χ)) s.
Proof. Fail now solve. Abort.
Lemma law_259 (φ ψ χ : LTL) : forall s, (φ U (ψ U χ)) s -> (φ U (ψ W χ)) s.
Proof. Fail now solve. Abort.
Lemma law_260 (φ ψ χ : LTL) : forall s, ((φ U ψ) U χ) s -> ((φ W ψ) U χ) s.
Proof. Fail now solve. Abort.
Lemma law_261 (φ ψ χ : LTL) : forall s, ((φ U ψ) U χ) s -> ((φ ∨ ψ) U χ) s.
Proof. Fail now solve. Abort.
Lemma law_262 (φ ψ χ : LTL) : forall s, ((φ W ψ) W χ) s -> ((φ ∨ ψ) W χ) s.
Proof. Fail now solve. Abort.
Lemma law_263 (φ ψ χ : LTL) : forall s, (φ W (ψ W χ)) s -> (φ W (ψ ∨ χ)) s.
Proof. Fail now solve. Abort.
Lemma law_264 (φ ψ χ : LTL) : forall s, (φ W (ψ W χ)) s -> ((φ ∨ ψ) W χ) s.
Proof. Fail now solve. Abort.
Lemma law_265 (φ ψ χ : LTL) : forall s, (φ W (ψ ∧ χ)) s -> ((φ W ψ) W χ) s.
Proof. Fail now solve. Abort.
Lemma law_266 (φ ψ : LTL) : forall s, ((¬ φ W ψ) ∨ (¬ ψ W φ)) s.
Proof. Fail now solve. Abort.
Lemma law_267 (φ ψ χ : LTL) : forall s, ((φ W ψ) ∧ (¬ ψ W χ)) s -> (φ W χ) s.
Proof. Fail now solve. Abort.

Lemma law_268 (φ ψ : LTL) : φ R ψ ≈ ¬(¬ φ U ¬ ψ).
Proof. now solve. Qed.
Lemma law_269 (φ ψ : LTL) : φ U ψ ≈ ¬(¬ φ R ¬ ψ).
Proof. now solve. Qed.
Lemma law_270 (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Proof. Fail now solve. Abort.
Lemma law_271 (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Proof. Fail now solve. Abort.
Lemma law_272 (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).
Proof. Fail now solve. Abort.
Lemma law_273 (φ ψ χ : LTL) : φ R (ψ ∨ χ) ≈ (φ R ψ) ∨ (φ R χ). (* ??? *)
Proof. Fail now solve. Abort.
Lemma law_274 (φ ψ χ : LTL) : (φ ∧ ψ) R χ ≈ (φ R χ) ∧ (ψ R χ). (* ??? *)
Proof. Fail now solve. Abort.
Lemma law_275 (φ ψ : LTL) : ◯ (φ R ψ) ≈ (◯ φ) R (◯ ψ).
Proof.
  solve.
  unfold Complement, not, In in *.
  - apply H with (x0 := x0); intuition eauto.
    + rewrite from_tail in H2.
      contradiction.
    + specialize (H1 _ H2).
      rewrite from_tail in H3.
      contradiction.
  - apply H with (x0 := x0).
    solve.
    + rewrite tail_from in H2.
      contradiction.
    + specialize (H1 _ H2).
      rewrite tail_from in H3.
      contradiction.
Qed.
Lemma law_276 (φ ψ : LTL) : □ ψ ≈ ⊥ R ψ.
Proof. Fail now solve. Abort.

Lemma law_277 (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Proof. now solve. Qed.
Lemma law_278 (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Proof. Fail now solve. Abort.
Lemma law_279 (φ ψ : LTL) : ¬(φ W ψ) ≈ (¬ φ M ¬ ψ).
Proof. Fail now solve. Abort.
Lemma law_280 (φ ψ : LTL) : ¬(φ M ψ) ≈ (¬ φ W ¬ ψ).
Proof. Fail now solve. Abort.

End LTL.
