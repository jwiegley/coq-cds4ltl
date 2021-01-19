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

Definition stream_eq (s t : Stream) : Prop := forall n, s n = t n.

Program Instance stream_eq_Equivalence : Equivalence stream_eq.
Next Obligation.
  specialize (H n).
  specialize (H0 n).
  now rewrite H, H0.
Qed.

Definition head (s : Stream) : a := s 0.

Lemma head_Proper : Proper (stream_eq ==> eq) head.
Proof.
  repeat intro.
  f_equal.
  extensionality n.
  apply H.
Qed.

Definition tail (s : Stream) : Stream := fun n => s (S n).

Program Instance tail_Proper : Proper (stream_eq ==> stream_eq) tail.
Next Obligation.
  repeat intro.
  f_equal.
  extensionality m.
  apply H.
Qed.

Definition cons (x : a) (s : Stream) : Stream := fun n =>
  match n with
  | O => x
  | S n' => s n'
  end.

Program Instance cons_Proper : Proper (eq ==> stream_eq ==> stream_eq) cons.
Next Obligation.
  repeat intro.
  f_equal; auto.
  extensionality m.
  apply H.
Qed.

Lemma cons_inj x s y u : cons x s = cons y u -> x = y /\ s = u.
Proof.
  unfold cons, stream_eq.
  intros.
  split.
  - now apply equal_f with (x0:=0) in H.
  - extensionality n.
    now apply equal_f with (x0:=S n) in H.
Qed.

Lemma head_cons x s : head (cons x s) = x.
Proof. now unfold head, cons. Qed.

Lemma tail_cons x s : tail (cons x s) = s.
Proof. now unfold tail, cons. Qed.

Definition LTL := Ensemble Stream.

Definition next (p : LTL) : LTL := fun s => p (tail s).

Program Instance next_Same_set:
  Proper (Same_set Stream ==> Same_set Stream) next.
Next Obligation.
  split; repeat intro; unfold In, next in *; now apply H.
Qed.

Program Instance next_Same_set_iff (p : LTL) :
  Proper (stream_eq ==> iff) p ->
  Proper (stream_eq ==> iff) (next p).
Next Obligation.
  split; repeat intro.
  - unfold next in *.
    now setoid_rewrite <- H0.
  - unfold next in *.
    now setoid_rewrite H0.
Qed.

Lemma next_cons_inv (p : LTL) x s : next p (cons x s) <-> p s.
Proof. now unfold next, tail, cons. Qed.

Lemma next_inv (p : LTL) (s : Stream) :
  next p s -> exists x s', stream_eq s (cons x s') /\ p s'.
Proof.
  unfold next, tail.
  intros.
  exists (head s).
  exists (tail s).
  split.
  - unfold stream_eq, cons, head, tail; intros.
    now induction n.
  - exact H.
Qed.

Definition examine (P : a -> LTL) : LTL := fun s => P (s O) s.

Program Instance examine_Same_set :
  Proper ((@eq a ==> Same_set Stream) ==> Same_set Stream) examine.
Next Obligation.
  intros.
  unfold respectful in H.
  split; repeat intro; unfold In, examine in *;
  specialize (H (x0 0) (x0 0) (reflexivity _));
  now apply H.
Qed.

Inductive until (p q : LTL) : LTL :=
  | until_hd s : q s -> until p q s
  | until_tl x s : p (cons x s) -> until p q s -> until p q (cons x s).

Program Instance until_Same_set :
  Proper (Same_set Stream ==> Same_set Stream ==> Same_set Stream) until.
Next Obligation.
  intros.
  split; repeat intro; unfold In in *.
  - induction H1.
    + left; now apply H0.
    + right; auto.
      now apply H.
  - induction H1.
    + left; now apply H0.
    + right; auto.
      now apply H.
Qed.

Program Instance until_Same_set_iff (p q : LTL) :
  Proper (stream_eq ==> iff) p ->
  Proper (stream_eq ==> iff) q ->
  Proper (stream_eq ==> iff) (until p q).
Next Obligation.
Abort.

Lemma until_inv (p q : LTL) s :
  until p q s -> q s \/ (p s /\ until p q (tail s)).
Proof.
  intros.
  dependent induction H; intuition.
Qed.

Lemma until_cons_inv (p q : LTL) x s :
  until p q (cons x s) -> q (cons x s) \/ (p (cons x s) /\ until p q s).
Proof.
  intros.
  dependent induction H; intuition.
  apply cons_inj in x.
  destruct x; subst.
  intuition.
Qed.

Inductive release (p q : LTL) : LTL :=
  | release_hd s : q s -> p s -> release p q s
  | release_tl x s : q (cons x s) -> release p q s -> release p q (cons x s).

Program Instance release_Same_set :
  Proper (Same_set Stream ==> Same_set Stream ==> Same_set Stream) release.
Next Obligation.
  intros.
  split; repeat intro; unfold In in *.
  - induction H1.
    + left.
      * now apply H0.
      * now apply H.
    + right; auto.
      now apply H0.
  - induction H1.
    + left.
      * now apply H0.
      * now apply H.
    + right; auto.
      now apply H0.
Qed.

Lemma release_inv (p q : LTL) s :
  release p q s -> q s /\ (p s \/ release p q (tail s)).
Proof.
  intros.
  dependent induction H; intuition.
Qed.

Lemma release_cons_inv (p q : LTL) x s :
  release p q (cons x s) -> q (cons x s) /\ (p (cons x s) \/ release p q s).
Proof.
  intros.
  dependent induction H; intuition;
  apply cons_inj in x;
  destruct x; subst; auto.
Qed.

Infix    "≈"       := (Same_set Stream)     (at level 100).
Notation "⊤"       := (Full_set Stream)     (at level 45).
Notation "⊥"       := (Empty_set Stream)    (at level 45).
Infix    "∧"       := (Intersection Stream) (at level 45).
Infix    "∨"       := (Union Stream)        (at level 45).
Notation "'X' x"   := (next x)              (at level 0).
Notation "p 'U' q" := (until p q)           (at level 45).
Notation "¬ p"     := (Complement Stream p) (at level 0).
Notation "p → q"   := (¬ p ∨ (p ∧ q))       (at level 45).
Notation "p 'R' q" := (release p q)         (at level 45).
Notation "◇ x"     := (⊤ U x)               (at level 0).
Notation "□ x"     := (⊥ R x)               (at level 0).

Definition weakUntil (p q : LTL) := (p U q) ∨ □ p.
Notation "p 'W' q" := (weakUntil p q) (at level 45).

Definition strongRelease (p q : LTL) := (p R q) ∧ ◇ p.
Notation "p 'M' q" := (strongRelease p q) (at level 45).

(** Principles of negation *)

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

Lemma not_inj (φ ψ : LTL) : (φ ≈ ψ) -> ¬φ ≈ ¬ψ.
Proof. intros; now rewrite H. Qed.

Lemma until_is_not_release (φ ψ : LTL) : Included _ (φ U ψ) (¬ (¬φ R ¬ψ)).
Proof.
  repeat intro.
  unfold In in *.
  dependent induction H.
  + dependent induction H0.
    * contradiction.
    * contradiction.
  + apply release_inv in H1.
    destruct H1.
    destruct H2.
    * contradiction.
    * rewrite tail_cons in H2.
      intuition.
Qed.

Lemma release_is_not_until (φ ψ : LTL) : Included _ (¬φ R ¬ψ) (¬ (φ U ψ)).
Proof.
  repeat intro.
  unfold In in *.
  dependent induction H.
  + dependent induction H1.
    * contradiction.
    * contradiction.
  + apply until_inv in H1.
    destruct H1.
    * contradiction.
    * destruct H1.
      rewrite tail_cons in H2.
      intuition.
Qed.

Lemma not_until (φ ψ : LTL) : ¬ (φ U ψ) ≈ ¬φ R ¬ψ.
Proof.
  rewrite <- Complement_Complement.
  apply not_inj.
  split; repeat intro; unfold In in *.
  - dependent induction H.
    + dependent induction H0.
      * contradiction.
      * contradiction.
    + apply release_inv in H1.
      destruct H1.
      destruct H2.
      * contradiction.
      * rewrite tail_cons in H2.
        intuition.
  - (* now need to prove ¬ (¬φ R ¬ψ) ≈ φ U ψ *)
Admitted.

Lemma not_release (φ ψ : LTL) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Admitted.

Lemma not_top : ¬(⊤) ≈ ⊥.
Proof.
  split; repeat intro.
  - elimtype False.
    apply H.
    now constructor.
  - unfold In in *.
    contradiction H.
Qed.

Lemma not_bottom : ¬(⊥) ≈ ⊤.
Proof.
  split; repeat intro.
  - now constructor.
  - contradiction H0.
Qed.

Lemma not_eventually (φ : LTL) : ¬(◇ φ) ≈ □ ¬φ.
Proof. now rewrite not_until, not_top. Qed.

Lemma not_always (φ : LTL) : ¬(□ φ) ≈ ◇ ¬φ.
Proof. now rewrite not_release, not_bottom. Qed.

Lemma not_weakUntil (φ ψ : LTL) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Proof.
  unfold weakUntil, strongRelease.
  rewrite not_or, not_always.
  now rewrite <- not_until.
Qed.

Lemma not_strongRelease (φ ψ : LTL) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Proof.
  unfold weakUntil, strongRelease.
  rewrite not_and, not_eventually.
  now rewrite <- not_release.
Qed.

(** Boolean equivalences *)

Lemma or_comm (φ ψ : LTL) : φ ∨ ψ ≈ ψ ∨ φ.
Proof. split; repeat intro; destruct H; now intuition. Qed.

Lemma or_assoc (φ ψ χ : LTL) : φ ∨ (ψ ∨ χ) ≈ (φ ∨ ψ) ∨ χ.
Proof.
  split; repeat intro.
  - destruct H.
    + now left; left.
    + destruct H.
      * now left; right.
      * now right.
  - destruct H.
    + destruct H.
      * now left.
      * now right; left.
    + now right; right.
Qed.

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
Proof.
  split; repeat intro.
  - destruct H.
    + split; now left.
    + destruct H; intuition.
  - destruct H.
    destruct H, H0; intuition.
Qed.

Lemma and_comm (φ ψ : LTL) : φ ∧ ψ ≈ ψ ∧ φ.
Proof.
  split; repeat intro.
  - destruct H.
    split; auto.
  - destruct H.
    split; auto.
Qed.

Lemma and_assoc (φ ψ χ : LTL) : φ ∧ (ψ ∧ χ) ≈ (φ ∧ ψ) ∧ χ.
Proof.
  split; repeat intro.
  - now destruct H, H0.
  - now destruct H, H.
Qed.

Lemma and_top (φ : LTL) : φ ∧ (⊤) ≈ φ.
Proof.
  split; repeat intro.
  - now destruct H.
  - now split.
Qed.

Lemma top_and (φ : LTL) : (⊤) ∧ φ ≈ φ.
Proof.
  split; repeat intro.
  - now destruct H.
  - now split.
Qed.

Lemma and_or (φ ψ χ : LTL) : φ ∧ (ψ ∨ χ) ≈ (φ ∧ ψ) ∨ (φ ∧ χ).
Proof.
  split; repeat intro.
  - destruct H, H0.
    + now left.
    + now right.
  - destruct H, H.
    + split; auto.
      now left.
    + split; auto.
      now right.
Qed.

(** Temporal equivalences *)

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof. reflexivity. Qed.

Lemma until_eventually (φ ψ : LTL) s : (φ U ψ) s -> (◇ ψ) s.
Proof.
  intros.
  dependent induction H; intuition.
  - now left.
  - right.
    + now constructor.
    + exact IHuntil.
Qed.

Lemma always_is (φ : LTL) s : (□ φ) s -> φ s.
Proof.
  intros.
  dependent induction H; intuition.
Qed.

Lemma always_tail (φ : LTL) s : (□ φ) s -> (□ φ) (tail s).
Proof.
  repeat intro.
  apply release_inv in H.
  now intuition.
Qed.

Lemma always_cons (φ : LTL) x s : (□ φ) (cons x s) -> (□ φ) s.
Proof.
  repeat intro.
  apply release_cons_inv in H.
  now intuition.
Qed.

Lemma eventually_tail (φ : LTL) s : (◇ φ) s -> φ s \/ (◇ φ) (tail s).
Proof.
  intros.
  dependent induction H; intuition.
Qed.

Lemma eventually_cons (φ : LTL) x s : (◇ φ) (cons x s) -> φ (cons x s) \/ (◇ φ) s.
Proof.
  intros.
  dependent induction H; intuition.
  apply cons_inj in x.
  destruct x; subst.
  intuition.
Qed.

Lemma eventually_always_until (φ ψ : LTL) s :
  (◇ ψ) s -> (□ φ) s -> (φ U ψ) s.
Proof.
  intros.
  dependent induction H; intuition.
  - now left.
  - clear H.
    right.
    + now apply always_is.
    + apply IHuntil.
      now apply always_cons in H1.
Qed.

(* ψ always remains true *)
Lemma always_release (ψ : LTL) : □ ψ ≈ ⊥ R ψ.
Proof. reflexivity. Qed.

Lemma always_not_eventually (ψ : LTL) : □ ψ ≈ ¬◇ ¬ψ.
Proof.
  now rewrite <- not_bottom, not_until, <- not_top, !Complement_Complement.
Qed.

Lemma release_until (φ ψ : LTL) : φ R ψ ≈ ¬(¬φ U ¬ψ).
Proof. now rewrite not_until, !Complement_Complement. Qed.

Lemma weakUntil_release_or (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Admitted.

Lemma release_weakUntil_and (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Admitted.

Lemma weakUntil_until_or (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Admitted.

Lemma strongRelease_not_weakUntil (φ ψ : LTL) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Admitted.

Lemma strongRelease_and_release (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Admitted.

Lemma strongRelease_release_and (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Admitted.

Lemma until_eventually_weakUntil (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof.
  rewrite weakUntil_until_or.
  split; repeat intro.
  - induction H.
    + split.
      * now left.
      * now left; left.
    + destruct IHuntil.
      split.
      * right; auto.
        now constructor.
      * now right.
  - destruct H.
    unfold In in H0.
    dependent induction H0.
    + destruct H0.
      * now left.
      * now apply eventually_always_until.
    + unfold In in H.
      apply until_cons_inv in H.
      destruct H; intuition.
      * now left.
      * right; auto.
Qed.

(** Distributivity *)

Lemma next_top : X (⊤) ≈ ⊤.
Proof. split; repeat intro; constructor. Qed.

Lemma next_bottom : X (⊥) ≈ ⊥.
Proof. split; repeat intro; contradiction. Qed.

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
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - inversion H; subst.
    now split.
  - inversion H; subst.
    now split.
Qed.

Lemma p_cons_tail (φ : LTL) s :
  φ (tail s) <-> exists x u, s = cons x u /\ φ u.
Proof.
  split; intros.
  - exists (head s).
    exists (tail s).
    split; auto.
    extensionality n.
    unfold cons, head, tail.
    induction n; intuition.
  - destruct H, H, H; subst.
    now rewrite tail_cons.
Qed.

Lemma next_until (φ ψ : LTL) : X (φ U ψ) ≈ (X φ) U (X ψ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - apply p_cons_tail in H.
    destruct H, H, H; subst.
    generalize dependent x0.
    dependent induction H0.
    + now left.
    + right.
      * now rewrite tail_cons.
      * apply IHuntil.
  - dependent induction H.
    + now left.
    + rewrite tail_cons in *.
      apply p_cons_tail in IHuntil.
      destruct IHuntil, H1, H1; subst.
      right; auto.
Qed.

Lemma next_release (φ ψ : LTL) : X (φ R ψ) ≈ (X φ) R (X ψ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - apply p_cons_tail in H.
    destruct H, H, H; subst.
    generalize dependent x0.
    dependent induction H0.
    + now left.
    + right.
      * now rewrite tail_cons.
      * apply IHrelease.
  - dependent induction H.
    + now left.
    + rewrite tail_cons in *.
      apply p_cons_tail in IHrelease.
      destruct IHrelease, H1, H1; subst.
      right; auto.
Qed.

Lemma next_eventually (φ : LTL) : X (◇ φ) ≈ ◇ (X φ).
Proof. now rewrite next_until, next_top. Qed.

Lemma next_always (φ : LTL) : X (□ φ) ≈ □ (X φ).
Proof. now rewrite next_release, next_bottom. Qed.

Lemma until_or (ρ φ ψ : LTL) : ρ U (φ ∨ ψ) ≈ (ρ U φ) ∨ (ρ U ψ).
Admitted.

Lemma and_until (ρ φ ψ : LTL) : (φ ∧ ψ) U ρ ≈ (φ U ρ) ∧ (ψ U ρ).
Admitted.

Lemma release_or (ρ φ ψ : LTL) : ρ R (φ ∨ ψ) ≈ (ρ R φ) ∨ (ρ R ψ).
Admitted.

Lemma and_release (ρ φ ψ : LTL) : (φ ∧ ψ) R ρ ≈ (φ R ρ) ∧ (ψ R ρ).
Admitted.

Lemma eventually_or (φ ψ : LTL) : ◇ (φ ∨ ψ) ≈ (◇ φ) ∨ (◇ ψ).
Proof. now rewrite until_or. Qed.

Lemma always_and (φ ψ : LTL) : □ (φ ∧ ψ) ≈ (□ φ) ∧ (□ ψ).
Admitted.

(** Special Temporal properties *)

Lemma until_idempotent_left  (φ ψ : LTL) : (φ U ψ) U ψ ≈ φ U ψ.
Proof.
  split; repeat intro.
  - induction H; auto.
    now left.
  - unfold In in *.
    dependent induction H.
    + now left.
    + right; auto.
      now right; auto.
Qed.

Lemma until_idempotent_right (φ ψ : LTL) : φ U (φ U ψ) ≈ φ U ψ.
Proof.
  split; repeat intro.
  - induction H; auto.
    now right.
  - unfold In in *.
    dependent induction H.
    + now left; left.
    + right; auto.
Qed.

Lemma eventually_idempotent (φ : LTL) : ◇ ◇ φ ≈ ◇ φ.
Proof. apply until_idempotent_right. Qed.

Lemma always_idempotent (φ : LTL) : □ □ φ ≈ □ φ.
Proof.
  rewrite !always_not_eventually.
  rewrite Complement_Complement.
  now rewrite eventually_idempotent.
Qed.

(** Expansion laws *)

Lemma expand_until (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ X (φ U ψ)).
Admitted.

Lemma expand_release (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ X (φ R ψ)).
Admitted.

Lemma expand_always (φ : LTL) : □ φ ≈ φ ∧ X (□ φ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - split.
    + now apply always_is.
    + unfold In.
      now apply always_tail.
  - destruct H.
    unfold In in *.
    apply p_cons_tail in H0.
    destruct H0, H0, H0; subst.
    now right.
Qed.

Lemma expand_eventually (φ : LTL) : ◇ φ ≈ φ ∨ X (◇ φ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - apply until_inv in H.
    destruct H.
    + now left.
    + destruct H.
      now right.
  - destruct H.
    + now left.
    + unfold In in H.
      apply p_cons_tail in H.
      destruct H, H, H; subst.
      now right.
Qed.

Lemma expand_weakUntil  (φ ψ : LTL) : φ W ψ ≈ ψ ∨ (φ ∧ X (φ W ψ)).
Admitted.

(** Absorption laws *)

Lemma asborb_eventually (φ : LTL) : ◇ □ ◇ φ ≈ □ ◇ φ.
Admitted.

Lemma asborb_always (φ : LTL) : □ ◇ □ φ ≈ ◇ □ φ.
Admitted.

End LTL.
