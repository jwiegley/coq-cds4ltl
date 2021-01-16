Require Import
  Program
  FunInd
  Coq.Lists.List
  Coq.Relations.Relation_Definitions
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Classes.Morphisms
  Coq.Logic.Classical
  Coq.Sets.Ensembles
  Coq.Sets.Classical_sets
  Coq.Setoids.Setoid
  Coq.omega.Omega
  Same_set.

Require Import Equations.Equations.
(*Require Import Equations.EqDec.*)

Open Scope program_scope.
Open Scope list_scope.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Section LTL.

Variable a : Type.              (* The type of entries in the trace *)

(* jww (2021-01-15): What if this were simply f a for any Representable f? *)
Definition Stream := nat -> a.

Definition cons (x : a) (s : Stream) : Stream := fun n =>
  match n with
  | O =>  x
  | S n' =>  s n'
  end.
Definition tail (s : Stream) : Stream := fun n => s (S n).

Definition LTL := Ensemble Stream.

Definition next (p : LTL) : LTL := fun s => p (tail s).

Add Parametric Morphism : next
  with signature (Same_set Stream ==> Same_set Stream)
    as next_Same_set.
Proof.
  split; repeat intro; unfold In, next in *; now apply H.
Qed.

Definition examine (P : a -> LTL) : LTL := fun s => P (s O) s.

Add Parametric Morphism : examine
  with signature ((@eq a ==> Same_set Stream) ==> Same_set Stream)
    as examine_Same_set.
Proof.
  intros.
  unfold respectful in H.
  split; repeat intro; unfold In, examine in *;
  specialize (H (x0 0) (x0 0) (reflexivity _));
  now apply H.
Qed.

Inductive until (p q : LTL) : Stream -> Prop :=
  | until_hd s : q s -> until p q s
  | until_tl x s : p (cons x s) -> until p q s -> until p q (cons x s).

Add Parametric Morphism : until
  with signature (Same_set Stream ==> Same_set Stream ==> Same_set Stream)
    as until_Same_set.
Proof.
  intros.
  split; repeat intro; unfold In in *.
  - induction H1.
    + left.
      now apply H0.
    + right; auto.
      now apply H.
  - induction H1.
    + left.
      now apply H0.
    + right; auto.
      now apply H.
Qed.

Notation "⊤"       := (Full_set Stream)     (at level 45).
Notation "⊥"       := (Empty_set Stream)    (at level 45).
Infix    "∧"       := (Intersection Stream) (at level 45).
Infix    "∨"       := (Union Stream)        (at level 45).
Notation "'X' x"   := (next x)              (at level 0).
Notation "p 'U' q" := (until p q)           (at level 45).

Notation "¬ p"     := (Complement Stream p) (at level 0).
Notation "p → q"   := (¬ p ∨ (p ∧ q))       (at level 45).
Notation "p 'R' q" := (¬ (¬ p U ¬ q))       (at level 45).
Notation "◇ x"     := (⊤ U x)               (at level 0).
Notation "□ x"     := (⊥ R x)               (at level 0).

Definition weakUntil (φ ψ : LTL) := (φ U ψ) ∨ □ φ.
Notation "p 'W' q" := (weakUntil p q) (at level 45).
Definition strongRelease (φ ψ : LTL) := (φ R ψ) ∧ ◇ φ.
Notation "p 'M' q" := (strongRelease p q) (at level 45).

(** Principles of negation *)

Infix    "≈"       := (Same_set Stream)     (at level 100).

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
  - rewrite <- (Complement_Complement Stream).
    intros s NAB.
    intro H.
    apply NAB.
    split.
    + rewrite <- (Complement_Complement Stream φ).
      intro H0.
      apply H.
      left; auto.
    + rewrite <- (Complement_Complement Stream ψ).
      intro H0.
      apply H.
      right; auto.
  - intros s NANB AB.
    destruct AB as [A1 B1].
    destruct NANB as [s NA | s NB]; auto.
Qed.

Lemma not_next (φ : LTL) : ¬(X φ) ≈ X ¬φ.
Proof. split; repeat intro; auto. Qed.

Lemma not_until (φ ψ : LTL) : ¬ (φ U ψ) ≈ ¬φ R ¬ψ.
Proof. now rewrite !Complement_Complement. Qed.

Lemma not_release (φ ψ : LTL) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Proof. now rewrite !Complement_Complement. Qed.

Lemma not_true : ¬(⊤) ≈ ⊥.
Proof.
  split; repeat intro.
  - elimtype False.
    apply H.
    now constructor.
  - unfold In in *.
    contradiction H.
Qed.

Lemma not_false : ¬(⊥) ≈ ⊤.
Proof.
  split; repeat intro.
  - now constructor.
  - contradiction H0.
Qed.

Lemma not_eventually (φ : LTL) : ¬(◇ φ) ≈ □ ¬φ.
Proof. now rewrite Complement_Complement, not_false. Qed.

Lemma not_always (φ : LTL) : ¬(□ φ) ≈ ◇ ¬φ.
Proof. now rewrite Complement_Complement, not_false. Qed.

Lemma not_weakUntil (φ ψ : LTL) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Proof.
  unfold weakUntil, strongRelease.
  rewrite not_or, not_always.
  now rewrite !Complement_Complement.
Qed.

Lemma not_strongRelease (φ ψ : LTL) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Proof.
  unfold weakUntil, strongRelease.
  rewrite not_and, not_eventually.
  now rewrite !Complement_Complement.
Qed.

(** Boolean equivalences *)

Lemma or_comm (φ ψ : LTL) : φ ∨ ψ ≈ ψ ∨ φ.
Proof. split; repeat intro; destruct H; now intuition. Qed.

Lemma or_assoc (φ ψ χ : LTL) : φ ∨ (ψ ∨ χ) ≈ (φ ∨ ψ) ∨ χ.
Admitted.

Lemma or_bottom (φ : LTL) : φ ∨ (⊥) ≈ φ.
Proof.
  split; repeat intro.
  - destruct H; auto.
    contradiction H.
  - now left.
Qed.

Lemma bottom_or (φ : LTL) : (⊥) ∨ φ ≈ φ.
Proof.
  split; repeat intro.
  - destruct H; auto.
    contradiction H.
  - now right.
Qed.

Lemma or_and (φ ψ χ : LTL) : φ ∨ (ψ ∧ χ) ≈ (φ ∨ ψ) ∧ (φ ∨ χ).
Admitted.

Lemma and_comm (φ ψ : LTL) : φ ∧ ψ ≈ ψ ∧ φ.
Admitted.

Lemma and_assoc (φ ψ χ : LTL) : φ ∧ (ψ ∧ χ) ≈ (φ ∧ ψ) ∧ χ.
Admitted.

Lemma and_top (φ : LTL) : φ ∧ (⊤) ≈ φ.
Admitted.

Lemma top_and (φ : LTL) : (⊤) ∧ φ ≈ φ.
Admitted.

Lemma and_or (φ ψ χ : LTL) : φ ∧ (ψ ∨ χ) ≈ (φ ∧ ψ) ∨ (φ ∧ χ).
Admitted.

(** Temporal equivalences *)

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof. reflexivity. Qed.

(* ψ always remains true *)
Lemma always_remains (ψ : LTL) : □ ψ ≈ ⊥ R ψ.
Proof. reflexivity. Qed.

Lemma always_not_eventually (ψ : LTL) : □ ψ ≈ ¬◇ ¬ψ.
Admitted.

Lemma until_eventually_or (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Admitted.

Lemma release_until (φ ψ : LTL) : φ R ψ ≈ ¬(¬φ U ¬ψ).
Proof. reflexivity. Qed.

Lemma weakUntil_release (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Admitted.

Lemma release_weakUntil (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Admitted.

Lemma weakUntil_until (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Admitted.

Lemma strongRelease_not_weakUntil (φ ψ : LTL) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Admitted.

Lemma strongRelease_release_or (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Admitted.

Lemma strongRelease_release (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Admitted.

(** Distributivity *)

Lemma next_or (φ ψ : LTL) : X (φ ∨ ψ) ≈ (X φ) ∨ (X ψ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - inversion H; subst.
    + left; auto.
    + right; auto.
  - inversion H; subst.
    + left; auto.
    + right; auto.
Qed.

Lemma next_and (φ ψ : LTL) : X (φ ∧ ψ) ≈ (X φ) ∧ (X ψ).
Admitted.

Lemma next_until (φ ψ : LTL) : X (φ U ψ) ≈ (X φ) U (X ψ).
Admitted.

Lemma next_release (φ ψ : LTL) : X (φ R ψ) ≈ (X φ) R (X ψ).
Admitted.

Lemma next_eventually (φ : LTL) : X (◇ φ) ≈ ◇ (X φ).
Admitted.

Lemma next_always (φ : LTL) : X (□ φ) ≈ □ (X φ).
Admitted.

Lemma eventually_or (φ ψ : LTL) : ◇ (φ ∨ ψ) ≈ (◇ φ) ∨ (◇ ψ).
Admitted.

Lemma always_and (φ ψ : LTL) : □ (φ ∧ ψ) ≈ (□ φ) ∧ (□ ψ).
Admitted.

Lemma until_or (ρ φ ψ : LTL) : ρ U (φ ∨ ψ) ≈ (ρ U φ) ∨ (ρ U ψ).
Admitted.

Lemma and_until (ρ φ ψ : LTL) : (φ ∧ ψ) U ρ ≈ (φ U ρ) ∧ (ψ U ρ).
Admitted.

Lemma release_or (ρ φ ψ : LTL) : ρ R (φ ∨ ψ) ≈ (ρ R φ) ∨ (ρ R ψ).
Admitted.

Lemma and_release (ρ φ ψ : LTL) : (φ ∧ ψ) R ρ ≈ (φ R ρ) ∧ (ψ R ρ).
Admitted.

(** Special Temporal properties *)

Lemma eventually_idempotent (φ : LTL) : ◇ ◇ φ ≈ ◇ φ.
Admitted.

Lemma always_idempotent (φ : LTL) : □ □ φ ≈ □ φ.
Admitted.

Lemma until_idempotent_left  (φ ψ : LTL) : (φ U ψ) U ψ ≈ φ U ψ.
Admitted.

Lemma until_idempotent_right (φ ψ : LTL) : φ U (φ U ψ) ≈ φ U ψ.
Admitted.

(** Expansion laws *)

Lemma expand_until (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ X(φ U ψ)).
Admitted.

Lemma expand_release (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ X(φ R ψ)).
Admitted.

Lemma expand_always (φ : LTL) : □ φ ≈ φ ∧ X(□ φ).
Admitted.

Lemma expand_eventually (φ : LTL) : ◇ φ ≈ φ ∨ X(◇ φ).
Admitted.

Lemma expand_weakUntil  (φ ψ : LTL) : φ W ψ ≈ ψ ∨ (φ ∧ X(φ W ψ)).
Admitted.

(** Absorption laws *)

Lemma asborb_eventually (φ : LTL) : ◇ □ ◇ φ ≈ □ ◇ φ.
Admitted.

Lemma asborb_always (φ : LTL) : □ ◇ □ φ ≈ ◇ □ φ.
Admitted.

End LTL.
