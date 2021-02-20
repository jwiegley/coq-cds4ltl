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
  Bool
  LTL.

Module StreamLTLW <: LinearTemporalLogicW.

Variable a : Type.

Infix    "∪"     := (Union _)        (at level 85, right associativity).
Notation "∅"     := (Empty_set _)    (at level 0, no associativity).
Infix    "∩"     := (Intersection _) (at level 80, right associativity).
Infix    "∈"     := (In _)           (at level 88, no associativity).
Notation "p ⊆ q" := (Included _ q p) (at level 89, no associativity).

Definition t := Ensemble (Stream a).

Definition not        := Complement (Stream a).
Definition or         := Union (Stream a).
Definition true       := Full_set (Stream a).
Definition false      := Empty_set (Stream a).
Definition and        := Intersection (Stream a).
Definition implies    := Included (Stream a).
Definition equivalent := Same_set (Stream a).

Program Instance implies_reflexive : Reflexive implies.
Next Obligation.
  unfold implies.
  now repeat intro.
Qed.

Program Instance implies_transitive : Transitive implies.
Next Obligation.
  unfold implies in *.
  repeat intro.
  now intuition.
Qed.

Program Instance not_respects_implies : Proper (implies --> implies) not | 1.
Next Obligation.
  unfold flip, implies.
  repeat intro.
  apply H0.
  now apply H.
Qed.

Program Instance or_respects_implies : Proper (implies ==> implies ==> implies) or.
Next Obligation.
  unfold implies, or.
  repeat intro.
  destruct H1; unfold Included, In in *.
  - left.
    now apply H.
  - right.
    now apply H0.
Qed.

Program Instance and_respects_implies : Proper (implies ==> implies ==> implies) and.
Next Obligation.
  unfold implies, and.
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

Notation "¬ p"    := (not p)         (at level 75, right associativity) : boolean_scope.
Infix    "∨"      := or              (at level 85, right associativity) : boolean_scope.
Notation "p ⇒ q"  := (¬ p ∨ q)       (at level 86, right associativity) : boolean_scope.
Notation "⊤"      := true            (at level 0, no associativity) : boolean_scope.
Notation "⊥"      := false           (at level 0, no associativity) : boolean_scope.
Infix    "⟹"     := implies         (at level 99, right associativity) : boolean_scope.
Infix    "≈"      := equivalent      (at level 90, no associativity) : boolean_scope.
Infix    "∧"      := and             (at level 80, right associativity) : boolean_scope.
Notation "p ≡ q"  := (p ⇒ q ∧ q ⇒ p) (at level 89, right associativity, only parsing) : boolean_scope.

Theorem or_inj p q : p ⟹ p ∨ q.
Proof. repeat intro; now left. Qed.

Theorem true_def p : p ∨ ¬p ≈ ⊤.
Proof.
  split; intros.
  - constructor.
  - repeat intro.
    pose proof (classic (In _ p x)).
    destruct H0.
      now left.
    now right.
Qed.

Theorem false_def p : ¬(p ∨ ¬p) ≈ ⊥.
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

Theorem or_comm p q : p ∨ q ≈ q ∨ p.
Proof.
  unfold or.
  now rewrite Union_commutative.
Qed.

Theorem or_assoc p q r : (p ∨ q) ∨ r ≈ p ∨ (q ∨ r).
Proof.
  unfold or.
  now rewrite Union_associative.
Qed.

Ltac inv H := inversion H; subst; clear H.

Theorem Intersection_Union {A : Type} p q :
  Same_set A (Intersection A p q)
             (Complement A (Union A (Complement A p) (Complement A q))).
Proof.
  split; repeat intro.
  - inv H.
    destruct H0.
    + now apply H.
    + now apply H.
  - rewrite <- (Complement_Complement A (Intersection A p q)).
    intro.
    apply H.
    unfold In, Complement, Logic.not in H0.
    assert (In A p x /\ In A q x → False).
      intros.
      apply H0.
      now constructor.
    apply not_and_or in H1.
    destruct H1.
      now left.
    now right.
Qed.

Theorem and_def p q : p ∧ q ≈ ¬(¬p ∨ ¬q).
Proof.
  split; repeat intro.
  - destruct H, H0; contradiction.
  - unfold and.
    rewrite Intersection_Union.
    exact H.
Qed.

Theorem huntington p q : ¬(¬p ∨ ¬q) ∨ ¬(¬p ∨ q) ≈ p.
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

Definition next : t -> t := λ p σ, [σ, 1] ⊨ p.

Program Instance next_respects_implies : Proper (implies ==> implies) next.
Next Obligation.
  repeat intro.
  apply H, H0.
Qed.

Definition until : t -> t -> t :=
  λ p q σ, ∃ k, [σ, k] ⊨ q /\ ∀ i, i < k -> [σ, i] ⊨ p.

Program Instance until_respects_implies :
  Proper (implies ==> implies ==> implies) until.
Next Obligation.
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

Theorem next_semantics : ∀ σ j p, [σ, j] ⊨ (◯ p) <-> [σ, j + 1] ⊨ p.
Proof.
  unfold next.
  split; intros.
  - rewrite PeanoNat.Nat.add_comm.
    now rewrite <- from_plus.
  - rewrite PeanoNat.Nat.add_comm in H.
    now rewrite <- from_plus in H.
Qed.

Theorem until_semantics : ∀ σ j p q,
  [σ, j] ⊨ (p U q) <->
  ∃ k, k ≥ j /\ [σ, k] ⊨ q /\ ∀ i, j ≤ i -> i < k -> [σ, i] ⊨ p.
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

Theorem (* 1 *) next_not p : ◯ ¬p ≈ ¬◯ p.
Proof.
  unfold next, not.
  split; repeat intro;
  now apply H.
Qed.

Theorem (* 2 *) next_impl p q : ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Proof.
  unfold next.
  split; repeat intro.
  - inv H.
    + now left.
    + now right.
  - inv H.
    + now left.
    + now right.
Qed.

Theorem (* 9 *) next_until p q : ◯ (p U q) ≈ (◯ p) U (◯ q).
Proof.
  unfold next, until.
  split; repeat intro; unfold In in *;
  now setoid_rewrite from_from.
Qed.

Theorem (* 10 *) until_expansion p q : p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Proof.
  unfold next, until, or, and.
  split; repeat intro; unfold In in *.
  - destruct H, H.
    generalize dependent p.
    generalize dependent q.
    generalize dependent x.
    induction x0; intros.
    + now left.
    + right.
      unfold In.
      constructor.
      apply (H0 0).
      * now apply PeanoNat.Nat.lt_0_succ.
      * unfold In.
        exists x0.
        split.
        ** now rewrite from_S.
        ** intros.
           rewrite from_S.
           apply H0.
           now apply (proj1 (PeanoNat.Nat.succ_lt_mono _ _)).
  - inv H.
    + exists 0.
      split; auto; intros.
      apply PeanoNat.Nat.nlt_0_r in H.
      contradiction.
    + destruct H0; unfold In in *.
      destruct H0, H0.
      rewrite from_S in H0.
      rewrite from_O in H0.
      setoid_rewrite from_S in H1.
      rewrite from_O in H1.
      exists (S x0).
      split; auto; intros.
      induction i; intros.
      * exact H.
      * apply H1.
        lia.
Qed.

Theorem (* 11 *) until_right_bottom p : p U ⊥ ≈ ⊥.
Proof.
  unfold next, until, or, and.
  split; repeat intro; unfold In in *.
  - destruct H, H.
    contradiction.
  - exists 0.
    split; auto; intros.
    lia.
Qed.

Theorem (* 12 *) until_left_or p q r : p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Proof.
  split; repeat intro; unfold In in *.
  unfold until, or in *.
  - destruct H.
    destruct H.
    inv H.
    + left.
      unfold In in *.
      exists x0.
      now split.
    + right.
      unfold In in *.
      exists x0.
      now split.
  - destruct H.
    destruct H.
    destruct H.
    + unfold until.
      exists x0.
      split.
      * now left.
      * intros.
        now apply H0.
    + destruct H.
      destruct H.
      unfold until.
      exists x0.
      split.
      * now right.
      * intros.
        now apply H0.
Qed.

Theorem (* 13 *) until_right_or p q r : (p U r) ∨ (q U r) ⟹ (p ∨ q) U r.
Proof.
  repeat intro; unfold In in *.
  unfold until, or in *.
  destruct H; unfold In in *.
  - destruct H.
    destruct H.
    exists x0.
    split; auto; intros.
    left.
    now intuition.
  - destruct H.
    destruct H.
    exists x0.
    split; auto; intros.
    right.
    now intuition.
Qed.

Theorem (* 14 *) until_left_and p q r : p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Proof.
  repeat intro; unfold In in *.
  unfold until, or in *.
  destruct H.
  destruct H.
  inv H.
  split; unfold In in *.
  - exists x0.
    now split.
  - exists x0.
    now split.
Qed.

Theorem (* 15 *) until_right_and p q r : (p ∧ q) U r ≈ (p U r) ∧ (q U r).
Proof.
  split; repeat intro;
  unfold until, In in *.
  - destruct H.
    destruct H.
    split; unfold In in *.
    + exists x0.
      split; auto; intros.
      specialize (H0 _ H1).
      inv H0.
      exact H2.
    + exists x0.
      split; auto; intros.
      specialize (H0 _ H1).
      inv H0.
      exact H3.
  - inv H.
    unfold In in *.
    destruct H0, H.
    destruct H1, H1.
    exists (min x0 x1).
    split; auto; intros.
    + now destruct (Min.min_dec x0 x1); rewrite e.
    + split.
      * apply H0.
        lia.
      * apply H2.
        lia.
Qed.

Theorem (* 16 *) until_impl_order p q r : (p U q) ∧ (¬q U r) ⟹ p U r.
Proof.
  repeat intro;
  unfold until, In in *.
  inv H.
  unfold In in *.
  destruct H0, H.
  destruct H1, H1.
  unfold not, Complement, Logic.not, In in H2.
  destruct (Compare_dec.le_lt_dec x1 x0).
  - exists x1.
    split; auto; intros.
    apply H0.
    lia.
  - elimtype False.
    now firstorder.
Qed.

Theorem (* 17 *) until_right_or_order p q r : p U (q U r) ⟹ (p ∨ q) U r.
Proof.
  repeat intro; unfold In in *.
  unfold until, or in *.
  destruct H; unfold In in *.
  destruct H.
  destruct H.
  destruct H.
  rewrite from_plus in H.
  exists (x1 + x0).
  split; auto; intros.
  destruct (Compare_dec.le_lt_dec x0 i).
  - right; unfold In.
    setoid_rewrite from_plus in H1.
    specialize (H1 (i - x0)).
    rewrite PeanoNat.Nat.sub_add in H1; auto.
    apply H1.
    lia.
  - left; unfold In.
    now apply H0.
Qed.

Theorem (* 18 *) until_right_and_order p q r : p U (q ∧ r) ⟹ (p U q) U r.
Proof.
  repeat intro; unfold In in *.
  unfold until, or in *.
  destruct H.
  destruct H.
  inv H.
  unfold In in *.
  exists x0.
  split; auto; intros.
  exists (x0 - i).
  rewrite from_plus.
  rewrite PeanoNat.Nat.sub_add.
  - split; auto; intros.
    rewrite from_plus.
    apply H0.
    lia.
  - lia.
Qed.

Lemma and_impl_iff_ p q r : (p ∧ q ⟹ r) ↔ (p ⟹ q ⇒ r).
Proof.
  split; repeat intro;
  specialize (H x).
  - destruct (classic (q x)).
    + right.
      apply H.
      now intuition.
    + now left.
  - destruct H0.
    destruct H; auto.
    contradiction.
Qed.

Lemma apply_ {p q x} : (Complement (Stream a) p ∪ q) x -> p x -> q x.
Proof.
  intros.
  now inv H.
Qed.

Theorem (* NEW *) not_until p q : ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).
Proof.
  split.
  - apply and_impl_iff_.
    assert (forall P, ¬¬P ≈ P). {
      split; intros;
      unfold not;
      rewrite Complement_Complement;
      reflexivity.
    }
    rewrite H; clear H.
    repeat intro.
    inv H.
    inv H0.
    clear H1.
    generalize dependent x.
    induction x0; intros.
    + destruct (classic (q x)).
      * left.
        exists 0.
        split; auto; intros.
        lia.
      * right.
        exists 0.
        split; auto; intros.
        split; auto; intros.
        lia.
    + specialize (IHx0 (from 1 x)).
      rewrite from_plus in IHx0.
      rewrite PeanoNat.Nat.add_1_r in IHx0.
      apply IHx0 in H; clear IHx0.
      destruct (classic (p x)).
      * inv H.
        ** inv H1.
           inv H.
           left.
           exists (S x1).
           setoid_rewrite from_plus in H1.
           rewrite PeanoNat.Nat.add_1_r in H1.
           split; auto; intros.
           specialize (H2 (Nat.pred i)).
           setoid_rewrite from_plus in H2.
           setoid_rewrite PeanoNat.Nat.add_1_r in H2.
           destruct i; auto.
           rewrite <- pred_Sn in *.
           apply H2.
           lia.
        ** inv H1.
           inv H.
           setoid_rewrite from_plus in H2.
           setoid_rewrite PeanoNat.Nat.add_1_r in H2.
           rewrite from_plus in H1.
           rewrite PeanoNat.Nat.add_1_r in H1.
           destruct (classic (q x)).
           *** left.
               exists 0.
               split; auto; intros.
               lia.
           *** right.
               exists (S x1).
               split; auto; intros.
               specialize (H2 (Nat.pred i)).
               destruct i; auto.
               rewrite <- pred_Sn in *.
               apply H2.
               lia.
      * inv H.
        ** inv H1.
           inv H.
           destruct (classic (q x)).
           *** left.
               exists 0.
               split; auto; intros.
               lia.
           *** right.
               exists 0.
               split; auto; intros.
               **** now split.
               **** lia.
        ** inv H1.
           inv H.
           setoid_rewrite from_plus in H2.
           setoid_rewrite PeanoNat.Nat.add_1_r in H2.
           rewrite from_plus in H1.
           rewrite PeanoNat.Nat.add_1_r in H1.
           destruct (classic (q x)).
           *** left.
               exists 0.
               split; auto; intros.
               lia.
           *** right.
               exists 0.
               split; auto; intros.
               **** now split.
               **** lia.
  - repeat intro.
    destruct H.
    inv H.
    inv H0.
    unfold In, not, Complement, Logic.not, In in *.
    split; unfold In.
    + eexists.
      split; eauto; intros.
      now constructor.
    + intro.
      destruct H0, H0.
      destruct (Compare_dec.le_lt_dec x1 x0).
      * eapply H1; eauto.
        destruct l.
        ** contradiction.
        ** lia.
      * apply H.
        now apply H3.
Qed.

Definition eventually : t -> t := any.
Definition always     : t -> t := every.
Definition wait       : t -> t -> t := fun p q => always p ∨ p U q.

Notation "◇ p"     := (eventually p)       (at level 75, right associativity) : ltl_scope.
Notation "□ p"     := (always p)           (at level 75, right associativity) : ltl_scope.
Notation "p 'W' q" := (wait p q)           (at level 79, right associativity) : ltl_scope.

Program Instance eventually_respects_implies : Proper (implies ==> implies) eventually.
Next Obligation.
  unfold eventually, any.
  repeat intro.
  unfold In in *.
  destruct H0.
  exists x1.
  apply H.
  exact H0.
Qed.

Program Instance always_respects_implies : Proper (implies ==> implies) always.
Next Obligation.
  unfold always, every.
  repeat intro.
  unfold In in *.
  apply H.
  now apply H0.
Qed.

Program Instance wait_respects_implies : Proper (implies ==> implies ==> implies) wait.
Next Obligation.
  unfold wait, always, every, until.
  repeat intro.
  unfold In in *.
  inv H1.
  - unfold In in *.
    left.
    unfold In in *.
    intros.
    apply H.
    now apply H2.
  - unfold In in *.
    right.
    unfold In in *.
    destruct H2.
    exists x2.
    destruct H1.
    split.
    + apply H0.
      exact H1.
    + intros.
      apply H.
      now apply H2.
Qed.

Theorem eventually_semantics : ∀ σ j p, [σ, j] ⊨ ◇ p.
Proof.
Admitted.

Theorem always_semantics : ∀ σ j p, [σ, j] ⊨ □ p.
Proof.
Admitted.

Theorem wait_semantics : ∀ σ j p q,
  [σ, j] ⊨ (p U q) <->
  ∃ k, k ≥ j /\ [σ, k] ⊨ q /\ ∀ i, j ≤ i -> i < k -> [σ, i] ⊨ p.
Proof.
Admitted.

Theorem evn_def p : ◇ p ≈ ⊤ U p.
Proof.
  unfold eventually, until, any.
  split; repeat intro; unfold In in *.
  - destruct H.
    exists x0.
    split; auto; intros.
    now split.
  - destruct H.
    exists x0.
    now destruct H.
Qed.

Theorem always_def p : □ p ≈ ¬◇ ¬p.
Proof.
  unfold always, eventually, until, any, every.
  split; repeat intro; unfold In in *.
  - destruct H0.
    apply H0.
    now apply H.
  - unfold not, Complement, Logic.not, In in H.
    apply NNPP.
    unfold Logic.not.
    intro.
    apply H.
    now exists i.
Qed.

(* This is provided by [LinearTemporalLogicFacts] below, I only proved it as a
   guide here to doing similar semantic proofs involving always. *)
Theorem always_induction_ p : □ (p ⇒ ◯ p) ⟹ p ⇒ □ p.
Proof.
  apply and_impl_iff_.
  unfold next, always, every.
  repeat intro.
  unfold In in *.
  inv H.
  pose proof (H0 i).
  induction i; intros.
  - now inv H; [contradiction|].
  - specialize (IHi (H0 i)).
    pose proof (apply_ (H0 i) IHi).
    clear -H2.
    rewrite <- PeanoNat.Nat.add_1_r.
    rewrite <- from_plus.
    rewrite <- from_from.
    now apply H2.
Qed.

Lemma not_until_eventually_ p : ¬(¬p U p) ⟹ ¬◇ p.
Proof.
  repeat intro.
  apply H; clear H.
  inv H0.
  generalize dependent x.
  induction x0; intros.
  - exists 0.
    split; auto; intros.
    lia.
  - specialize (IHx0 (from 1 x)).
    rewrite from_plus in IHx0.
    rewrite PeanoNat.Nat.add_1_r in IHx0.
    apply IHx0 in H; clear IHx0.
    destruct (classic (p x)).
    + exists 0.
      split; auto; intros.
      lia.
    + inv H.
      inv H1.
      rewrite from_plus in H.
      rewrite PeanoNat.Nat.add_1_r in H.
      setoid_rewrite from_plus in H2.
      setoid_rewrite PeanoNat.Nat.add_1_r in H2.
      exists (S x1).
      split; auto; intros.
      destruct i; auto.
      apply H2.
      lia.
Qed.

(* p p p p p p p q  p U q ∧ r U s ∧ r U (p ∧ s)
   r r r r r s s s

   p p p p p q q q  p U q ∧ r U s ∧ p U (q ∧ r)
   r r r r r r r s

   p p p p p p p q  p U q ∧ r U s
   r r r r r r r s
 *)
Theorem until_race p q r s : p U q ∧ r U s ⟹ p U (q ∧ r) ∨ r U (p ∧ s).
Proof.
  repeat intro.
  inv H.
  inv H0; inv H1.
  inv H; inv H0.
  destruct (classic (x0 < x1)).
  - left.
    + exists x0.
      split.
      * split; auto.
        apply H3.
        lia.
      * intros.
        apply H2.
        lia.
  - destruct (classic (x0 = x1)).
    subst.
    lia.
    right.
    + exists x1.
      split.
      * split; auto.
        apply H2.
        lia.
      * intros.
        apply H2.
        lia.
    + exists x
      split.
      * split; auto.
        apply H2.
        lia.
Admitted.

Theorem always_until_and_ind_ p q r :
  □ (p ⇒ (◯ p ∧ q) ∨ r) ⟹ p ⇒ □ q ∨ q U r.
Proof.
  apply and_impl_iff_.
  intros x H.
  inv H.
  destruct (classic ((¬r U r) x)).
  - inv H.
    inv H2.
    right.
    exists x0.
    split; auto; intros.
    enough ([x, i] ⊨ q /\ [x, i] ⊨ p).
      now inv H2.
    pose proof (H0 i).
    induction i; intros.
    + pose proof (apply_ H4 H1).
      split; auto; intros.
      inv H4.
      * contradiction.
      * inv H6.
        ** now inv H4.
        ** specialize (H3 0).
           now intuition.
    + assert (i < x0) by lia.
      destruct (IHi H5 (H0 i)).
      pose proof (apply_ (H0 i) H7).
      inv H8.
      * inv H9.
        unfold next, In in H8.
        rewrite from_plus in H8.
        pose proof (apply_ (H0 (S i)) H8).
        split; auto.
        inv H9.
        ** now inv H11.
        ** specialize (H3 _ H2).
           contradiction.
      * specialize (H3 _ H5).
        contradiction.
  - apply not_until_eventually_ in H.
    left.
    intro.
    enough ([x, i] ⊨ q /\ [x, i] ⊨ p).
      now inv H2.
    pose proof (H0 i).
    induction i; intros.
    + inv H2; [contradiction|].
      inv H3; [now inv H2|].
      apply not_ex_all_not with (n:=0) in H.
      contradiction.
    + destruct (IHi (H0 i)).
      pose proof (apply_ (H0 i) H4).
      inv H5.
      * inv H6.
        unfold next, In in H5.
        rewrite from_plus in H5.
        pose proof (apply_ H2 H5).
        split; auto.
        inv H6.
        ** now inv H8.
        ** apply not_ex_all_not with (n:=S i) in H.
           contradiction.
      * apply not_ex_all_not with (n:=i) in H.
        contradiction.
Qed.

Theorem always_and_until_ p q r : □ p ∧ q U r ⟹ (p ∧ q) U (p ∧ r).
Proof.
  unfold until, next, always, every, or, and, not.
  repeat intro.
  inv H.
  unfold In in *.
  destruct H1.
  exists x0.
  destruct H.
  split.
  - split.
    + now apply H0.
    + now apply H.
  - split; intros.
    + now apply H0.
    + now apply H1.
Qed.

Theorem wait_def p q : p W q ≈ □ p ∨ p U q.
Proof. reflexivity. Qed.

Definition F p q := □ (p ⇒ □ q).

Theorem Dummett p : F (F p p) p ⟹ (◇ □ p ⇒ □ p).
Proof.
Admitted.

End StreamLTLW.

Module StreamLTL <: LinearTemporalLogic.

Include StreamLTLW.

Definition release        : t -> t -> t := fun x _ => x.
Definition strong_release : t -> t -> t := fun x _ => x.

Notation "p 'R' q" := (release p q)        (at level 79, right associativity) : ltl_scope.
Notation "p 'M' q" := (strong_release p q) (at level 79, right associativity) : ltl_scope.

Program Instance release_respects_implies :
  Proper (implies ==> implies ==> implies) release.
Next Obligation.
Admitted.

Program Instance strong_release_respects_implies :
  Proper (implies ==> implies ==> implies) strong_release.
Next Obligation.
Admitted.

Theorem release_def p q : p R q ≈ ¬(¬p U ¬q).
Proof.
Admitted.

Theorem strong_release_def p q : p M q ≈ q U (p ∧ q).
Proof.
Admitted.

End StreamLTL.
