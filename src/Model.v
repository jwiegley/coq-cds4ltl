Set Warnings "-local-declaration".

Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Coq.Sets.Powerset_facts
  Coq.Sets.Classical_sets
  Coq.Sets.Ensembles
  Coq.Classes.Morphisms
  Same_set
  Stream
  LTL.

Module StreamLTL <: LinearTemporalLogic.

Variable a : Type.

Definition t := Ensemble (Stream a).

Definition not   := Complement (Stream a).
Definition or    := Union (Stream a).
Definition impl  := Included (Stream a).
Definition true  := Full_set (Stream a).
Definition false := Empty_set (Stream a).
Definition eqv   := Same_set (Stream a).
Definition and   := Intersection (Stream a).

Program Instance impl_reflexive : Reflexive impl.
Next Obligation.
  unfold impl.
  now intro.
Qed.

Program Instance impl_transitive : Transitive impl.
Next Obligation.
  unfold impl, Included in *.
  repeat intro.
  now intuition.
Qed.

Program Instance not_respects_impl : Proper (impl --> impl) not | 1.
Next Obligation.
  unfold flip, impl.
  repeat intro.
  apply H0.
  now apply H.
Qed.

Program Instance or_respects_impl : Proper (impl ==> impl ==> impl) or.
Next Obligation.
  unfold impl, or.
  repeat intro.
  destruct H1; unfold Included, In in *.
  - left.
    now apply H.
  - right.
    now apply H0.
Qed.

Program Instance and_respects_impl : Proper (impl ==> impl ==> impl) and.
Next Obligation.
  unfold impl, and.
  repeat intro.
  destruct H1; unfold Included, In in *.
  constructor.
  - now apply H.
  - now apply H0.
Qed.

Declare Scope boolean_scope.
Bind Scope boolean_scope with t.
Delimit Scope boolean_scope with boolean.
Open Scope boolean_scope.

Notation "¬ p"    := (not p)    (at level 75, right associativity) : boolean_scope.
Infix    "∨"      := or         (at level 85, right associativity) : boolean_scope.
Notation "p ⇒ q"  := (¬ p ∨ q)  (at level 86, right associativity) : boolean_scope.
Notation "⊤"      := true       (at level 0, no associativity) : boolean_scope.
Notation "⊥"      := false      (at level 0, no associativity) : boolean_scope.
Notation "p ⟹ q" := (impl p q) (at level 99, right associativity) : boolean_scope.
Notation "p ≈ q"  := (eqv p q)  (at level 90, no associativity) : boolean_scope.
Infix    "∧"       := and             (at level 80, right associativity) : boolean_scope.
Notation "p ≡ q"   := (p ⇒ q ∧ q ⇒ p) (at level 89, right associativity, only parsing) : boolean_scope.

Theorem impl_denote (p q : t) : (p ⟹ q) <-> (p ≈ ⊤ -> q ≈ ⊤).
Proof.
  split; intros.
  - destruct H0.
    split; intros.
    + constructor.
    + unfold impl in H.
      now transitivity p; auto.
  - unfold impl.
    repeat intro.
    rewrite H.
    + constructor.
    + split.
      * constructor.
      * repeat intro.
        (* We run afoul of a mismatch between existential witnesses *)
Admitted.

Theorem true_def (p : t) : p ∨ ¬p ≈ ⊤.
Proof.
  split; intros.
  - constructor.
  - (* The goal is the axiom of the excluded middle. *)
Admitted.

Theorem false_def (p : t) : ¬(p ∨ ¬p) ≈ ⊥.
Proof.
  split; intros.
  - rewrite true_def.
    repeat intro.
    destruct H.
    now constructor.
  - rewrite true_def.
    repeat intro.
    contradiction.
Qed.

Theorem or_comm (p q : t) : p ∨ q ≈ q ∨ p.
Proof.
  unfold or.
  now rewrite Union_commutative.
Qed.

Theorem or_assoc (p q r : t) : (p ∨ q) ∨ r ≈ p ∨ (q ∨ r).
Proof.
  unfold or.
  now rewrite Union_associative.
Qed.

Theorem and_def (p q : t) : p ∧ q ≈ ¬(¬p ∨ ¬q).
Proof.
  unfold and, or, not.
  split; repeat intro.
  - destruct H, H0; contradiction.
  - unfold Complement, In, Logic.not in *.
    (* The goal should be a simple fact of logic. *)
Admitted.

Theorem huntington (p q : t) : ¬(¬p ∨ ¬q) ∨ ¬(¬p ∨ q) ≈ p.
Proof.
  split; intros.
  - rewrite <- (Complement_Complement _ q) at 2.
    rewrite <- !and_def.
    unfold or.
    rewrite <- Distributivity.
    rewrite true_def.
    repeat intro.
    now destruct H.
  - rewrite <- (Complement_Complement _ q) at 2.
    rewrite <- !and_def.
    unfold or.
    rewrite <- Distributivity.
    rewrite true_def.
    repeat intro.
    constructor; auto.
    now constructor.
Qed.

Definition next : t -> t := λ p s,（s, 1）⊨ p.

Program Instance next_respects_impl : Proper (impl ==> impl) next.
Next Obligation.
  unfold impl, next.
  repeat intro.
  apply H, H0.
Qed.

Definition until : t -> t -> t :=
  λ p q s, ∃ k,（s, k）⊨ q /\ ∀ i, i < k ->（s, i）⊨ p.

Program Instance until_respects_impl : Proper (impl ==> impl ==> impl) until.
Next Obligation.
  unfold impl, until.
  repeat intro.
  destruct H1.
  exists x2.
  destruct H1.
  split.
  - now apply H0.
  - intros.
    apply H.
    now apply H2.
Qed.

Declare Scope ltl_scope.
Bind Scope ltl_scope with t.
Delimit Scope ltl_scope with ltl.
Open Scope boolean_scope.
Open Scope ltl_scope.

Notation "◯ p"     := (next p)    (at level 75, right associativity) : ltl_scope.
Notation "p 'U' q" := (until p q) (at level 79, right associativity) : ltl_scope.

Theorem next_semantics : ∀ σ j p,（σ, j）⊨ (◯ p) <->（σ, j + 1）⊨ p.
Proof.
  unfold next.
  split; intros.
  - rewrite PeanoNat.Nat.add_comm.
    now rewrite <- from_plus.
  - rewrite PeanoNat.Nat.add_comm in H.
    now rewrite <- from_plus in H.
Qed.

Theorem until_semantics : ∀ σ j p q,
 （σ, j）⊨ (p U q) <-> ∃ k, k ≥ j /\（σ, k）⊨ q /\ ∀ i, j ≤ i -> i < k ->（σ, i）⊨ p.
Proof.
  unfold until.
  repeat setoid_rewrite from_plus.
  split; intros.
  - destruct H.
    destruct H.
    exists (x + j).
    split.
      lia.
    split; auto.
    intros.
    specialize (H0 (i - j)).
    rewrite PeanoNat.Nat.sub_add in H0.
      apply H0.
      lia.
    lia.
  - destruct H.
    destruct H.
    destruct H0.
    exists (x - j).
    rewrite PeanoNat.Nat.sub_add.
      split; auto.
      intros.
      specialize (H1 (i + j)).
      apply H1.
        lia.
      lia.
    lia.
Qed.

Theorem (* 1 *) next_not (p : t) : ◯ ¬p ≈ ¬◯ p.
Proof.
Admitted.

Theorem (* 2 *) next_impl (p q : t) : ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Proof.
Admitted.

Theorem (* 9 *) next_until (p q : t) : ◯ (p U q) ≈ (◯ p) U (◯ q).
Proof.
Admitted.

Theorem (* 10 *) until_expansion (p q : t) : p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Proof.
Admitted.

Theorem (* 11 *) until_right_bottom (p : t) : p U ⊥ ≈ ⊥.
Proof.
Admitted.

Theorem (* 12 *) until_left_or (p q r : t) : p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Proof.
Admitted.

Theorem (* 13 *) until_right_or (p q r : t) : (p U r) ∨ (q U r) ⟹ (p ∨ q) U r.
Proof.
Admitted.

Theorem (* 14 *) until_left_and (p q r : t) : p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Proof.
Admitted.

Theorem (* 15 *) until_right_and (p q r : t) : (p ∧ q) U r ≈ (p U r) ∧ (q U r).
Proof.
Admitted.

Theorem (* 16 *) until_impl_order (p q r : t) : (p U q) ∧ (¬q U r) ⟹ p U r.
Proof.
Admitted.

Theorem (* 17 *) until_right_or_order (p q r : t) : p U (q U r) ⟹ (p ∨ q) U r.
Proof.
Admitted.

Theorem (* 18 *) until_right_and_order (p q r : t) : p U (q ∧ r) ⟹ (p U q) U r.
Proof.
Admitted.

(** jww (2021-02-08): This axiom is just an idea a work in progress *)
Theorem (* NEW *) until_continue (p q : t) : q ∧ p U ◯ ¬q ⟹ p U (q ∧ ◯ ¬q).
Proof.
Admitted.

Theorem (* NEW *) not_until (p q : t) : ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).
Proof.
Admitted.

Definition eventually : t -> t := any.
Definition always : t -> t := every.
Definition wait : t -> t -> t.
Definition release : t -> t -> t.
Definition strong_release : t -> t -> t.

Notation "◇ p"     := (eventually p)       (at level 75, right associativity) : ltl_scope.
Notation "□ p"     := (always p)           (at level 75, right associativity) : ltl_scope.
Notation "p 'W' q" := (wait p q)           (at level 79, right associativity) : ltl_scope.
Notation "p 'R' q" := (release p q)        (at level 79, right associativity) : ltl_scope.
Notation "p 'M' q" := (strong_release p q) (at level 79, right associativity) : ltl_scope.

Program Instance eventually_respects_impl : Proper (impl ==> impl) eventually.
Program Instance always_respects_impl : Proper (impl ==> impl) always.
Program Instance wait_respects_impl : Proper (impl ==> impl ==> impl) wait.
Program Instance release_respects_impl : Proper (impl ==> impl ==> impl) release.
Program Instance strong_release_respects_impl : Proper (impl ==> impl ==> impl) strong_release.

Theorem evn_def (p : t) : ◇ p ≈ ⊤ U p.
Proof.
Admitted.

Theorem always_def (p : t) : □ p ≈ ¬◇ ¬p.
Proof.
Admitted.

Theorem always_until_and_ind (p q r : t) :
  □ (p ⇒ (◯ p ∧ q) ∨ r) ⟹ p ⇒ □ q ∨ q U r.
Proof.
Admitted.

Theorem wait_def (p q : t) : p W q ≈ □ p ∨ p U q.
Proof.
Admitted.

Theorem release_def (p q : t) : p R q ≈ ¬(¬p U ¬q).
Proof.
Admitted.

Theorem strong_release_def (p q : t) : p M q ≈ p U (q ∧ p).
Proof.
Admitted.

Include LinearTemporalLogicFacts.

End StreamLTL.
