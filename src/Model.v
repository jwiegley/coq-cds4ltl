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

Module Type StreamType.

Parameter a : Type.              (* The type of entries in the trace *)

End StreamType.

Module StreamLTLW (S : StreamType) <: LinearTemporalLogicW.

Definition t := Ensemble (Stream S.a).

Infix    "∪"     := (Union _)        (at level 85, right associativity).
Notation "∅"     := (Empty_set _)    (at level 0, no associativity).
Infix    "∩"     := (Intersection _) (at level 80, right associativity).
Notation "p ∈ q" := (In _ q p)       (at level 88, no associativity).
Notation "p ⊆ q" := (Included _ q p) (at level 89, no associativity).

Definition not        := Complement (Stream S.a).
Definition or         := Union (Stream S.a).
Definition true       := Full_set (Stream S.a).
Definition false      := Empty_set (Stream S.a).
Definition and        := Intersection (Stream S.a).
Definition implies    := Included (Stream S.a).
Definition equivalent := Same_set (Stream S.a).

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

Theorem Union_Complement {A : Type} p q :
  Same_set A (Complement A (Union A p q))
             (Intersection A (Complement A p) (Complement A q)).
Proof.
  split; repeat intro.
  - rewrite Intersection_Union.
    now rewrite !Complement_Complement.
  - rewrite Intersection_Union in H.
    now rewrite !Complement_Complement in H.
Qed.

Theorem Intersection_Complement {A : Type} p q :
  Same_set A (Complement A (Intersection A p q))
             (Union A (Complement A p) (Complement A q)).
Proof.
  split; repeat intro.
  - rewrite Intersection_Union in H.
    now rewrite !Complement_Complement in H.
  - destruct H0.
    destruct H; now apply H.
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

Theorem (* 10 *) until_expand p q : p U q ≈ q ∨ (p ∧ ◯ (p U q)).
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

Theorem (* 11 *) until_false p : p U ⊥ ≈ ⊥.
Proof.
  unfold next, until, or, and.
  split; repeat intro; unfold In in *.
  - destruct H, H.
    contradiction.
  - exists 0.
    split; auto; intros.
    lia.
Qed.

Theorem (* NEW *) looped p : ◯ ¬p U p ⟹ p.
Proof.
  unfold next, not, Complement, Logic.not.
  repeat intro.
  inv H.
  inv H0.
  unfold In in *.
  setoid_rewrite from_plus in H1.
  simpl plus in H1.
  destruct (Compare_dec.le_lt_dec x0 0).
    assert (x0 = 0) by lia.
    subst.
    exact H.
  assert (Nat.pred x0 < x0) by lia.
  specialize (H1 _ H0).
  rewrite PeanoNat.Nat.succ_pred_pos in H1; [|lia].
  contradiction.
Qed.

Theorem (* NEW *) until_and_not_ p q : p U q ∧ ¬q ⟹ (p ∧ ¬q) U (p ∧ ¬q ∧ ◯ q).
Proof.
  repeat intro.
  inv H.
  inv H0.
  inv H.
  generalize dependent x.
  induction x0; intros; [contradiction|].
  destruct (classic (from 1 x ∈ q)).
  - exists 0.
    split.
    + split.
      * apply H2; lia.
      * split.
        ** exact H1.
        ** exact H.
    + lia.
  - specialize (IHx0 (from 1 x) H).
    rewrite from_plus in IHx0.
    rewrite PeanoNat.Nat.add_1_r in IHx0.
    assert (∀ i : nat, i < x0 → [from 1 x, i] ⊨ p). {
      intros.
      rewrite from_plus.
      rewrite PeanoNat.Nat.add_1_r.
      apply H2; lia.
    }
    specialize (IHx0 H0 H3).
    clear -IHx0 H1 H2.
    inv IHx0.
    inv H.
    inv H0.
    inv H4.
    setoid_rewrite from_plus in H3.
    setoid_rewrite PeanoNat.Nat.add_1_r in H3.
    rewrite from_plus in *.
    rewrite PeanoNat.Nat.add_1_r in *.
    unfold next, In in H5.
    exists (S x1).
    split.
    + split; auto.
      split; auto.
    + intros.
      destruct (Compare_dec.le_lt_dec i 0).
      * assert (i = 0) by lia.
        subst.
        split; auto.
        apply H2; lia.
      * assert (Nat.pred i < x1) by lia.
        specialize (H3 (Nat.pred i) H6).
        inv H3.
        rewrite PeanoNat.Nat.succ_pred_pos in *; try lia.
        split; auto.
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

Theorem (* NEW *) until_and_until p q r s :
  p U q ∧ r U s ⟹ (p ∧ r) U ((q ∧ r) ∨ (p ∧ s) ∨ (q ∧ s)).
Proof.
  repeat intro.
  inv H.
  inv H0; inv H1.
  inv H; inv H0.
  destruct (classic (x0 < x1)).
  - exists x0.
    + split.
      * left.
        split; auto.
        apply H3; lia.
      * intros.
        split.
        ** apply H2; lia.
        ** apply H3; lia.
  - destruct (classic (x0 = x1)).
    + subst.
      exists x1.
      split.
      * right; right.
        now split.
      * intros.
        split.
        ** apply H2; lia.
        ** apply H3; lia.
    + exists x1.
      split.
      * right; left.
        split; auto.
        apply H2; lia.
      * intros.
        split.
        ** apply H2; lia.
        ** apply H3; lia.
Qed.

Theorem (* 17 *) until_left_or_order p q r : p U (q U r) ⟹ (p ∨ q) U r.
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

Theorem (* 170 *) not_until p q : ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).
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

Notation "◇ p" := (eventually p) (at level 75, right associativity) : ltl_scope.
Notation "□ p" := (always p)     (at level 75, right associativity) : ltl_scope.

Definition wait : t -> t -> t := fun p q => □ p ∨ p U q.

Notation "p 'W' q" := (wait p q) (at level 79, right associativity) : ltl_scope.

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

Theorem (* 38 *) evn_def p : ◇ p ≈ ⊤ U p.
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

Theorem (* 54 *) always_def p : □ p ≈ ¬◇ ¬p.
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

Theorem (* 169 *) wait_def p q : p W q ≈ □ p ∨ p U q.
Proof. reflexivity. Qed.

Definition F p q := □ (p ⇒ □ q).

Theorem Dummett p : F (F p p) p ⟹ (◇ □ p ⇒ □ p).
Abort.

End StreamLTLW.

Module StreamLTL (S : StreamType) <: LinearTemporalLogic.

Include StreamLTLW S.

Definition release        : t -> t -> t := fun p q => q W (q ∧ p).
Definition strong_release : t -> t -> t := fun p q => q U (q ∧ p).

Notation "p 'R' q" := (release p q)        (at level 79, right associativity) : ltl_scope.
Notation "p 'M' q" := (strong_release p q) (at level 79, right associativity) : ltl_scope.

Program Instance release_respects_implies :
  Proper (implies ==> implies ==> implies) release.
Next Obligation.
  unfold release.
  do 6 intro.
  now rewrite H, H0.
Qed.

Program Instance strong_release_respects_implies :
  Proper (implies ==> implies ==> implies) strong_release.
Next Obligation.
  unfold strong_release.
  do 6 intro.
  now rewrite H, H0.
Qed.

Theorem release_def p q : p R q ≈ ¬(¬p U ¬q).
Proof.
  unfold release, wait.
Admitted.

Theorem strong_release_def p q : p M q ≈ q U (p ∧ q).
Proof.
  unfold strong_release.
  assert (q ∧ p ≈ p ∧ q). {
    split; repeat intro.
    - destruct H.
      now constructor.
    - destruct H.
      now constructor.
  }
  split; intros.
  - now rewrite H.
  - now rewrite <- H.
Qed.

End StreamLTL.
