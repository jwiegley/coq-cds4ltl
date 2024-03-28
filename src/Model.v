Set Warnings "-local-declaration".

Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Coq.Sets.Powerset_facts
  Coq.Sets.Classical_sets
  Coq.Sets.Ensembles
  Coq.Classes.Morphisms
  CDS4LTL.Same_set
  CDS4LTL.MinBool
  CDS4LTL.Bool
  CDS4LTL.MinLTL
  CDS4LTL.LTL.

Ltac matches :=
  match goal with
  | [ H : ∃ _, _ |- ∃ _, _ ] =>
      let x := fresh "x" in
      destruct H as [x ?]; exists x
  end.

Ltac as_if :=
  repeat match goal with
  | [ H : ?P ?X |- ?P ?Y ] =>
      let H0 := fresh "H0" in
      assert (X = Y) as H0 by lia;
      now rewrite <- H0
  | [ H : ∀ _ : ?T, _ |- ∀ _ : ?T, _ ] =>
      let n := fresh "n" in
      intro n; specialize (H n)
  | [ |- _ < _ ] => lia
  | [ |- _ <= _ ] => lia
  | [ |- _ > _ ] => lia
  | [ |- _ >= _ ] => lia
  | [ H : _ < 0 |- _ ] => lia
  end.

Ltac reduce :=
  unfold Included, In in *; intros;
  repeat (match goal with
          | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2 in H; subst
          | [ H : Union _ _ _ _ |- _ ] => inversion H; subst; clear H
          | [ H : Union _ _ _ |- _ ] => inversion H; subst; clear H
          | [ H : Intersection _ _ _ _ |- _ ] => inversion H; subst; clear H
          | [ H : Intersection _ _ _ |- _ ] => inversion H; subst; clear H
          | [ H : _ ∧ _ |- _ ] => inversion H; subst; clear H
          | [ H : _ * _ |- _ ] => inversion H; subst; clear H
          | [ H : ∃ _, _ |- _ ] => inversion H; subst; clear H
          | [ H : { _ : _ | _ } |- _ ] => inversion H; subst; clear H
          | [ H : { _ : _ & _ } |- _ ] => inversion H; subst; clear H
          end; subst;
          unfold Included, In, Complement, Logic.not in *; intros);
  simpl in *.

Ltac just_math :=
  simpl; reduce; try extensionality n; f_equal; lia.

Ltac inv H := inversion H; subst; clear H; reduce.

Ltac equality := intuition congruence.

Module ModelMinBool <: MinimalBooleanLogic.

Definition t := Ensemble nat.

Infix    "∪"     := (Union _)        (at level 85, right associativity).
Notation "∅"     := (Empty_set _)    (at level 0, no associativity).
Notation "p ∈ q" := (In _ q p)       (at level 88, no associativity).
Notation "p ⊆ q" := (Included _ p q) (at level 89, no associativity).

Definition not        := Complement nat.
Definition or         := Union nat.
Definition true       := Full_set nat.
Definition false      := Empty_set nat.
Definition implies    := Included nat.
Definition equivalent := Same_set nat.

#[global]
Program Instance implies_Reflexive : Reflexive implies.
Next Obligation.
  unfold implies.
  now repeat intro.
Qed.

#[global]
Program Instance implies_Transitive : Transitive implies.
Next Obligation.
  unfold implies in *.
  repeat intro.
  now intuition.
Qed.

#[global]
Program Instance not_respects_implies : Proper (implies --> implies) not | 1.
Next Obligation.
  unfold flip, implies.
  repeat intro.
  apply H0.
  now apply H.
Qed.

#[global]
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

#[global]
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

Theorem implies_inclusion : forall A P Q, P ⊆ Q ↔ ∀ x : A, x ∈ P -> x ∈ Q.
Proof. split; intros; intuition. Qed.

Theorem implies_true : forall P, P ⟹ ⊤.
Proof.
  repeat intro.
  constructor.
Qed.

Theorem false_implies : forall P, ⊥ ⟹ P.
Proof.
  repeat intro.
  contradiction H.
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

(** These next three theorems are missing from the standard library. *)
Theorem Intersection_Union {A : Type} p q :
  Same_set A (Intersection A p q)
             (Complement A (Union A (Complement A p) (Complement A q))).
Proof.
  split; repeat intro.
  - inv H;
    now apply H.
  - rewrite <- (Complement_Complement A (Intersection A p q)).
    intro.
    apply H.
    unfold In, Complement, Logic.not in H0.
    assert (In A p x ∧ In A q x → False).
      intros.
      apply H0.
      now constructor.
    apply not_and_or in H1.
    destruct H1.
      now left.
    now right.
Qed.

Theorem Complement_Union {A : Type} p q :
  Same_set A (Complement A (Union A p q))
             (Intersection A (Complement A p) (Complement A q)).
Proof.
  split; repeat intro.
  - rewrite Intersection_Union.
    now rewrite !Complement_Complement.
  - rewrite Intersection_Union in H.
    now rewrite !Complement_Complement in H.
Qed.

Theorem Complement_Intersection {A : Type} p q :
  Same_set A (Complement A (Intersection A p q))
             (Union A (Complement A p) (Complement A q)).
Proof.
  split; repeat intro.
  - rewrite Intersection_Union in H.
    now rewrite !Complement_Complement in H.
  - destruct H0.
    destruct H; now apply H.
Qed.

Theorem Excluded_Middle {A : Type} p :
  Same_set A (p ∪ Complement A p) (Full_set A).
Proof.
  split; repeat intro.
  - now constructor.
  - destruct (classic (In A p x)).
    + now left.
    + now right.
Qed.

Corollary Complement_Full {A : Type} :
  Same_set A (Complement A (Full_set A)) (Empty_set A).
Proof.
  split; repeat intro.
  - exfalso.
    apply H.
    now constructor.
  - contradiction.
Qed.

Theorem huntington p q : ¬(¬p ∨ ¬q) ∨ ¬(¬p ∨ q) ≈ p.
Proof.
  unfold not, or.
  split; intros.
  - rewrite !Complement_Union.
    rewrite !Complement_Complement.
    rewrite <- Distributivity.
    rewrite Excluded_Middle.
    repeat intro.
    now inv H.
  - rewrite !Complement_Union.
    rewrite !Complement_Complement.
    rewrite <- Distributivity.
    rewrite Excluded_Middle.
    repeat intro.
    split; auto.
    now constructor.
Qed.

Theorem or_inj p q : p ⟹ p ∨ q.
Proof. repeat intro; now left. Qed.

Theorem true_def p : p ∨ ¬p ≈ ⊤.
Proof. now apply Excluded_Middle. Qed.

Theorem false_def p : ¬(p ∨ ¬p) ≈ ⊥.
Proof.
  unfold or, not.
  rewrite Excluded_Middle.
  now apply Complement_Full.
Qed.

Theorem empty_implication p : ¬ Inhabited _ p -> p ⊆ ¬p.
Proof.
  repeat intro.
  firstorder.
Qed.

Theorem non_empty_implication p : Inhabited _ p -> ¬(p ⊆ ¬p).
Proof.
  repeat intro.
  destruct H.
  specialize (H0 _ H).
  contradiction.
Qed.

End ModelMinBool.

Module ModelBool <: BooleanLogic.

Module MB := ModelMinBool.
Include MB.

Infix    "∩"     := (Intersection _) (at level 80, right associativity).

Definition and   := Intersection nat.

Infix    "∧"     := and             (at level 80, right associativity) : boolean_scope.
Notation "p ≡ q" := (p ⇒ q ∧ q ⇒ p) (at level 89, right associativity, only parsing) : boolean_scope.

#[global]
Program Instance and_respects_implies : Proper (implies ==> implies ==> implies) and.
Next Obligation.
  unfold implies, and.
  repeat intro.
  destruct H1; unfold Included, In in *.
  constructor.
  - now apply H.
  - now apply H0.
Qed.

Theorem and_def p q : p ∧ q ≈ ¬(¬p ∨ ¬q).
Proof.
  split; repeat intro.
  - destruct H, H0; contradiction.
  - unfold and.
    rewrite Intersection_Union.
    exact H.
Qed.

End ModelBool.

Module ModelMinLTL <: MinimalLinearTemporalLogic.

Module B := ModelBool.
Include B.

Definition shift (k : nat) : t → t := λ p n, p (n + k).
Arguments shift k _ /.

Lemma shift_comm i j s : shift i (shift j s) = shift j (shift i s).
Proof. just_math. Qed.

Lemma shift_plus_in i j s : shift (i + j) s = shift i (shift j s).
Proof. just_math. Qed.

Lemma shift_zero s : shift 0 s = s.
Proof. just_math. Qed.

Corollary shift_one n s : shift 1 s n = s (n + 1).
Proof. reflexivity. Qed.

Lemma shift_succ n i s : shift (S i) s n = shift i s (n + 1).
Proof. just_math. Qed.

Lemma shift_plus_out i j n s : shift i s (j + n) = shift (i + n) s j.
Proof. just_math. Qed.

Corollary shift_push i P : shift i (λ n, P n) = λ n, P (n + i).
Proof. reflexivity. Qed.

Lemma univ (P Q : t) : (λ n, P n) ≈ (λ n, Q n) ↔ (∀ n, P n ↔ Q n).
Proof.
  split; intros.
  - split; intros; now apply H.
  - split; unfold Included, In in *; intros;
    now apply H.
Qed.

Definition next : t → t := shift 1.
Definition until : t → t → t :=
  λ p q n, ∃ k, shift k q n /\ ∀ i, i < k → shift i p n.

#[global]
Declare Scope ltl_scope.
Bind Scope ltl_scope with t.
Delimit Scope ltl_scope with ltl.
Open Scope boolean_scope.
Open Scope ltl_scope.

Notation "◯ p"     := (next p)    (at level 75, right associativity) : ltl_scope.
Notation "p 'U' q" := (until p q) (at level 79, right associativity) : ltl_scope.

#[global]
Program Instance next_respects_implies : Proper (implies ==> implies) next.
Next Obligation.
  unfold respectful.
  intros.
  unfold implies in *.
  repeat intro.
  apply H, H0.
Qed.

#[global]
Program Instance until_respects_implies :
  Proper (implies ==> implies ==> implies) until.
Next Obligation.
  repeat intro.
  destruct H1, H1.
  exists x2.
  split.
  - now apply H0.
  - intros.
    apply H.
    now apply H2.
Qed.

Theorem (* 1 *) next_not p : ◯ ¬p ≈ ¬◯ p.
Proof.
  split; repeat intro;
  now apply H.
Qed.

Theorem (* 2 *) next_impl p q : ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Proof.
  unfold next.
  split; repeat intro;
  inv H; first [ now left | now right ].
Qed.

Theorem (* 9 *) next_until p q : ◯ (p U q) ≈ (◯ p) U (◯ q).
Proof.
  unfold next, until.
  rewrite shift_push.
  apply univ; intros.
  split; intro; matches; reduce;
  split; as_if.
Qed.

Theorem (* 10 *) until_expand p q : p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Proof.
  unfold next, until, or, and.
  rewrite shift_push.
  split; reduce.
  - destruct x0.
    + left; as_if.
    + right; reduce.
      split.
      * rewrite plus_n_O.
        apply H1; lia.
      * reduce.
        exists x0.
        split.
        ** as_if.
        ** intros.
           rewrite <- PeanoNat.Nat.add_assoc.
           apply H1; lia.
  - exists 0.
    split; auto; intros;
    as_if.
  - exists (S x0).
    split; [as_if|].
    intros.
    destruct i.
    + as_if.
    + specialize (H2 i ltac:(lia)).
      as_if.
Qed.

Theorem (* 11 *) until_false p : p U ⊥ ⟹ ⊥.
Proof.
  unfold until, implies; reduce.
  contradiction.
Qed.

Theorem (* NEW *) looped p : ◯ ¬p U p ⟹ p.
Proof.
  unfold next, not, until, implies; reduce.
  destruct x0.
  - as_if.
  - exfalso.
    eapply H1; eauto.
    as_if.
Qed.

Theorem (* 12 *) until_left_or p q r : p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Proof.
  split; repeat intro;
  unfold until, or in *; reduce.
  - inv H.
    + left.
      reduce.
      exists x0.
      now split.
    + right.
      reduce.
      exists x0.
      now split.
  - exists x0.
    split.
    * now left.
    * now as_if.
  - exists x0.
    split.
    * now right.
    * intros.
      now apply H1.
Qed.

Theorem (* 14 *) until_left_and p q r : p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Proof.
  repeat intro;
  unfold until, and, or in *; reduce.
  split; reduce;
  exists x0;
  now split.
Qed.

Theorem (* NEW *) until_and_until p q r s :
  p U q ∧ r U s ⟹ (p ∧ r) U ((q ∧ r) ∨ (p ∧ s) ∨ (q ∧ s)).
Proof.
  repeat intro;
  unfold until, and, or in *; reduce.
  destruct (classic (x1 < x0)).
  - exists x1.
    + split.
      * left.
        split; auto.
        apply H2; lia.
      * intros.
        split.
        ** apply H3; lia.
        ** apply H2; lia.
  - destruct (classic (x0 = x1)).
    + subst.
      exists x1.
      split.
      * right; right.
        now split.
      * intros.
        split.
        ** apply H3; lia.
        ** apply H2; lia.
    + exists x0.
      split.
      * right; left.
        split; auto.
        apply H3; lia.
      * intros.
        split.
        ** apply H3; lia.
        ** apply H2; lia.
Qed.

Theorem (* 17 *) until_left_or_order p q r : p U (q U r) ⟹ (p ∨ q) U r.
Proof.
  unfold implies, until, or in *; reduce.
  reduce.
  exists (x1 + x0).
  split; [as_if|].
  intros.
  destruct (Compare_dec.le_lt_dec x0 i).
  + right.
    specialize (H2 (i - x0) ltac:(lia)).
    as_if.
  + left.
    now apply H1.
Qed.

Theorem (* 18 *) until_right_and_order p q r : p U (q ∧ r) ⟹ (p U q) U r.
Proof.
  repeat intro; unfold until, and in *; reduce.
  inv H; reduce.
  exists x0.
  split; auto; intros.
  exists (x0 - i).
  split; [as_if|].
  intros.
  specialize (H1 (i + i0) ltac:(lia)).
  as_if.
Qed.

Lemma and_impl_iff_ p q r : (p ∧ q ⟹ r) ↔ (p ⟹ q ⇒ r).
Proof.
  split; repeat intro;
  unfold and, implies in *; reduce.
  specialize (H x).
  - destruct (classic (q x)).
    + right.
      apply H.
      now intuition.
    + now left.
  - destruct (H _ H1); auto.
    contradiction.
Qed.

Theorem (* 170 *) not_until p q : ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).
Proof.
  split.
  - apply and_impl_iff_.
    assert (∀ P, ¬¬P ≈ P). {
      split; intros;
      unfold not;
      now rewrite Complement_Complement.
    }
    rewrite H; clear H.
    repeat intro.
    inv H; clear H1.
    generalize dependent x.
    (* This the only theorem that requires induction! *)
    induction x0; intros.
    + destruct (classic (q x)).
      * left.
        exists 0.
        split; auto; intros;
        simpl; as_if.
      * right.
        exists 0.
        split; auto; intros.
        ** split; intro;
           now apply H0; as_if.
        ** lia.
    + destruct (classic (p x)).
      * simpl in *.
        rewrite <- PeanoNat.Nat.add_succ_comm in H.
        apply IHx0 in H; clear IHx0.
        inv H; inv H1.
        ** left.
           exists (S x1).
           split; [simpl in *; as_if|].
           intros.
           specialize (H2 (Nat.pred i)).
           simpl in H2.
           destruct i; [simpl; as_if|].
           simpl in *.
           rewrite <- plus_n_Sm.
           apply H2.
           lia.
        ** destruct (classic (q x)).
           *** left.
               exists 0.
               split; auto; intros;
               simpl; as_if.
           *** right.
               exists (S x1).
               split; auto; intros.
               **** rewrite shift_succ.
                    now rewrite PeanoNat.Nat.add_1_r.
               **** specialize (H2 (Nat.pred i)).
                    destruct i; reduce.
                    ***** inv H1; reduce.
                          intro.
                          apply H.
                          as_if.
                    ***** rewrite <- plus_n_Sm.
                          apply H2.
                          lia.
      * destruct (classic (q x)).
        ** left.
           exists 0.
           split; auto; intros;
           simpl; as_if.
        ** right.
           exists 0.
           split; auto; intros.
           *** split; intro.
               **** now apply H0; as_if.
               **** now apply H1; as_if.
           *** lia.
  - repeat intro.
    inv H; reduce; inv H.
    split; reduce.
    + eexists.
      split; eauto; intros.
      now constructor.
    + intro.
      destruct H; reduce.
      destruct (Compare_dec.le_lt_dec x1 x0).
      * eapply H1; eauto.
        destruct l.
        ** contradiction.
        ** lia.
      * apply H0.
        now apply H4.
Qed.

Theorem (* NEW *) impl_link p q : (p ⟹ q) ↔ (p ⇒ q) ≈ ⊤.
Proof.
  unfold implies, or, not, equivalent, true.
  split; repeat intro.
  - split; repeat intro.
    + constructor.
    + now destruct (classic (x ∈ p)); intuition.
  - inv H; reduce.
    specialize (H2 _ (Full_intro _ x)).
    inv H2; intuition.
Qed.

End ModelMinLTL.

Module ModelLTLW <: LinearTemporalLogicW.

Module ML := ModelMinLTL.
Include ML.
Module Import MLF := MinimalLinearTemporalLogicFacts ML.

Definition eventually : t → t := λ p n, ∃ k, shift k p n.
Definition always     : t → t := λ p n, ∀ k, shift k p n.

Notation "◇ p" := (eventually p) (at level 75, right associativity) : ltl_scope.
Notation "□ p" := (always p)     (at level 75, right associativity) : ltl_scope.

Definition wait : t → t → t := λ p q, □ p ∨ p U q.

Notation "p 'W' q" := (wait p q) (at level 79, right associativity) : ltl_scope.

#[global]
Program Instance eventually_respects_implies : Proper (implies ==> implies) eventually.
Next Obligation.
  unfold eventually;
  repeat intro; reduce.
  exists x1.
  apply H.
  exact H1.
Qed.

#[global]
Program Instance always_respects_implies : Proper (implies ==> implies) always.
Next Obligation.
  unfold always;
  repeat intro; reduce.
  apply H.
  now apply H0.
Qed.

#[global]
Program Instance wait_respects_implies : Proper (implies ==> implies ==> implies) wait.
Next Obligation.
  unfold wait, always, until.
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
    exists x2.
    split.
    + apply H0.
      exact H2.
    + intros.
      apply H.
      now apply H3.
Qed.

Theorem (* 38 *) evn_def p : ◇ p ≈ ⊤ U p.
Proof.
  unfold eventually, until.
  split; repeat intro; reduce;
  exists x0; auto.
  split; auto; intros.
  constructor.
Qed.

Theorem (* 54 *) always_def p : □ p ≈ ¬◇ ¬p.
Proof.
  unfold always, eventually, until.
  split; repeat intro; reduce.
  - apply H1.
    now apply H.
  - apply NNPP.
    intro.
    apply H.
    now exists k.
Qed.

Theorem (* 169 *) wait_def p q : p W q ≈ □ p ∨ p U q.
Proof. reflexivity. Qed.

(* This unfolds to:
   ∀ x, (∀ y, p y ⟹ q y) → (◯ p) x ⟹ (◯ q) x *)
Theorem (* NEW *) external p q : (p ⟹ q) → ◯ p ⟹ ◯ q.
Proof.
  unfold implies, next;
  repeat intro; reduce.
  apply H, H0.
Qed.

Theorem (* NEW *) impossible p q : (p ⇒ q) ⟹ (◯ p ⇒ ◯ q).
Proof.
  rewrite <- next_impl.
  unfold implies, next, always.
  repeat intro; reduce.
  destruct H.
Abort.

(* Without □ this unfolds to:

     ∀ x, (p x ⇒ q x) ⟹ (◯ p) x ⇒ (◯ q) x

   but with □ it unfolds to the same structure as [external]:

     ∀ x, (∀ y, p y ⇒ q y) ⟹ (◯ p) x ⇒ (◯ q) x
 *)
Theorem (* NEW *) internal p q : □ (p ⇒ q) ⟹ (◯ p ⇒ ◯ q).
Proof.
  rewrite <- next_impl.
  unfold implies, next, always.
  repeat intro; reduce.
  apply H.
Qed.

(* Temporal deduction is Theorem (2.1.6) of Kröger and Merz [20], who also
   give the justiﬁcation. Note that if you assume P in a step of an LTL proof
   of Q, you have not proved that P ⇒ Q, but rather that □ P ⇒ Q. *)
Theorem (* 82 *) temporal_deduction p q : (p ⟹ q) → (□ p ⟹ □ q).
Proof.
  unfold implies, always;
  intros; reduce.
  apply H, H0.
Qed.

End ModelLTLW.

Module ModelLTL <: LinearTemporalLogic.

Module LW := ModelLTLW.
Include LW.

Module Import MBF := MinimalBooleanLogicFacts LW.
Module Import LWF := LinearTemporalLogicWFacts LW.

Theorem (* NEW *) impossible p : (p ≈ ⊤) → (□ p ≈ ⊤).
Proof.
  intros.
  now rewrite H, law_64.
Qed.

Definition release        : t → t → t := λ p q, q W (q ∧ p).
Definition strong_release : t → t → t := λ p q, q U (q ∧ p).

Notation "p 'R' q" := (release p q)        (at level 79, right associativity) : ltl_scope.
Notation "p 'M' q" := (strong_release p q) (at level 79, right associativity) : ltl_scope.

#[global]
Program Instance release_respects_implies :
  Proper (implies ==> implies ==> implies) release.
Next Obligation.
  unfold release.
  do 6 intro.
  now rewrite H, H0.
Qed.

#[global]
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
  assert (q ∧ p ≈ p ∧ q). {
    split; repeat intro;
    destruct H;
    now constructor.
  }
  rewrite H.
  rewrite law_173.
  rewrite !not_not.
  now rewrite wait_def.
Qed.

Theorem strong_release_def p q : p M q ≈ q U (p ∧ q).
Proof.
  unfold strong_release.
  assert (q ∧ p ≈ p ∧ q). {
    split; repeat intro;
    destruct H;
    now constructor.
  }
  split; intros.
  - now rewrite H.
  - now rewrite <- H.
Qed.

End ModelLTL.
