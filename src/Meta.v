Set Warnings "-local-declaration".

Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Coq.Sets.Powerset_facts
  Coq.Sets.Classical_sets
  Coq.Sets.Ensembles
  Coq.Classes.Morphisms
  Bool
  LTL.

Module Type StreamType.

Parameter t : Type.

End StreamType.

Module StreamLTLW (S : StreamType) <: LinearTemporalLogicW.

Definition t := S.t -> nat -> Prop.

Definition not        := fun (p : t) s j => ~ p s j.
Definition or         := fun (p q : t) s j => p s j \/ q s j.
Definition true       := fun (_ : S.t) (_ : nat) => True.
Definition false      := fun (_ : S.t) (_ : nat) => False.
Definition and        := fun (p q : t) s j => p s j /\ q s j.
Definition implies    := fun (p q : t) => forall s j, p s j -> q s j.
Definition equivalent := fun (p q : t) => implies p q /\ implies q p.

#[local] Obligation Tactic := firstorder.

Program Instance implies_reflexive : Reflexive implies.
Program Instance implies_transitive : Transitive implies.
Program Instance not_respects_implies : Proper (implies --> implies) not | 1.
Program Instance or_respects_implies : Proper (implies ==> implies ==> implies) or.
Program Instance and_respects_implies : Proper (implies ==> implies ==> implies) and.

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
Proof. now firstorder. Qed.

Theorem true_def p : p ∨ ¬p ≈ ⊤.
Proof.
  split; repeat intro; firstorder.
  exact (classic (p s j)).
Qed.

Theorem false_def p : ¬(p ∨ ¬p) ≈ ⊥.
Proof. now firstorder. Qed.

Theorem or_comm p q : p ∨ q ≈ q ∨ p.
Proof. now firstorder. Qed.

Theorem or_assoc p q r : (p ∨ q) ∨ r ≈ p ∨ (q ∨ r).
Proof. now firstorder. Qed.

Ltac inv H := inversion H; subst; clear H.

Theorem and_def p q : p ∧ q ≈ ¬(¬p ∨ ¬q).
Proof.
  split; repeat intro.
  - firstorder;
    now apply NNPP.
  - apply not_or_and in H;
    now apply NNPP; firstorder.
Qed.

Theorem huntington p q : ¬(¬p ∨ ¬q) ∨ ¬(¬p ∨ q) ≈ p.
Proof.
  split; repeat intro.
  - apply or_not_and in H.
    now apply NNPP; firstorder.
  - apply not_and_or.
    now firstorder.
Qed.

Declare Scope ltl_scope.
Bind Scope ltl_scope with t.
Delimit Scope ltl_scope with ltl.
Open Scope boolean_scope.
Open Scope ltl_scope.

Definition next : t -> t := λ p s j, p s (S j).

Program Instance next_respects_implies : Proper (implies ==> implies) next.

Definition until : t -> t -> t :=
  λ p q s j, ∃ k, j ≤ k /\ q s k /\ ∀ i, j ≤ i -> i < k -> p s i.

Program Instance until_respects_implies :
  Proper (implies ==> implies ==> implies) until.

Notation "◯ p"     := (next p)    (at level 75, right associativity) : ltl_scope.
Notation "p 'U' q" := (until p q) (at level 79, right associativity) : ltl_scope.

Theorem (* 1 *) next_not p : ◯ ¬p ≈ ¬◯ p.
Proof. now firstorder. Qed.

Theorem (* 2 *) next_impl p q : ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Proof. now firstorder. Qed.

Theorem (* 9 *) next_until p q : ◯ (p U q) ≈ (◯ p) U (◯ q).
Proof.
  split; repeat intro; firstorder.
  - exists (Nat.pred x).
    firstorder.
    + lia.
    + unfold next.
      rewrite <- Lt.S_pred_pos; auto.
      lia.
    + apply H1; lia.
  - exists (S x).
    firstorder.
    + lia.
    + specialize (H1 (Nat.pred i)).
      unfold next in H1.
      rewrite <- Lt.S_pred_pos in H1; firstorder.
      * apply H1; lia.
      * lia.
Qed.

Theorem (* 10 *) until_expand p q : p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Proof.
  split; repeat intro; firstorder.
  - generalize dependent j.
    induction x; intros.
    + assert (j = 0) by lia.
      subst.
      now left.
    + admit.
  - exists j; firstorder; lia.
Admitted.

Theorem (* 11 *) until_false p : p U ⊥ ≈ ⊥.
Proof. now firstorder. Qed.

Theorem (* NEW *) looped p : ◯ ¬p U p ⟹ p.
Proof.
  repeat intro; firstorder.
Admitted.

Theorem (* 12 *) until_left_or p q r : p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Proof. now firstorder. Qed.

Theorem (* 14 *) until_left_and p q r : p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Proof. now firstorder. Qed.

Theorem (* NEW *) until_and_until p q r s :
  p U q ∧ r U s ⟹ (p ∧ r) U ((q ∧ r) ∨ (p ∧ s) ∨ (q ∧ s)).
Proof.
  repeat intro; firstorder.
  exists (Nat.min x x0).
  split.
  - lia.
  - split.
    + destruct (Compare_dec.lt_dec x x0).
      * right; left; split.
        ** apply H4; lia.
        ** rewrite PeanoNat.Nat.min_l; auto; lia.
      * assert (x0 <= x) by lia; clear n.
        destruct (PeanoNat.Nat.eq_dec x x0).
        ** subst.
           rewrite PeanoNat.Nat.min_l; auto.
           right; right; split; auto.
        ** rewrite PeanoNat.Nat.min_r; auto.
           left; split; auto.
           apply H2; lia.
    + split; intros.
      * apply H4; lia.
      * apply H2; lia.
Qed.

Theorem (* 17 *) until_left_or_order p q r : p U (q U r) ⟹ (p ∨ q) U r.
Proof.
  repeat intro; firstorder.
Admitted.

Theorem (* 18 *) until_right_and_order p q r : p U (q ∧ r) ⟹ (p U q) U r.
Proof.
  repeat intro; firstorder.
Admitted.

Theorem (* 170 *) not_until p q : ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).
Proof.
  split; repeat intro; firstorder.
Admitted.

Definition eventually : t -> t := fun p s j => ∃ k, j ≤ k /\ p s k.
Definition always     : t -> t := fun p s j => ∀ k, j ≤ k -> p s k.
Definition wait       : t -> t -> t := fun p q => always p ∨ p U q.

Notation "◇ p"     := (eventually p) (at level 75, right associativity) : ltl_scope.
Notation "□ p"     := (always p)     (at level 75, right associativity) : ltl_scope.
Notation "p 'W' q" := (wait p q)     (at level 79, right associativity) : ltl_scope.

Program Instance eventually_respects_implies : Proper (implies ==> implies) eventually.
Program Instance always_respects_implies : Proper (implies ==> implies) always.
Program Instance wait_respects_implies : Proper (implies ==> implies ==> implies) wait.

Theorem (* 38 *) evn_def p : ◇ p ≈ ⊤ U p.
Proof. now firstorder. Qed.

Theorem (* 54 *) always_def p : □ p ≈ ¬◇ ¬p.
Proof.
  split; repeat intro; firstorder.
  specialize (H k).
  simpl in H.
  apply not_and_or in H.
  firstorder.
  now apply NNPP.
Qed.

Theorem (* 169 *) wait_def p q : p W q ≈ □ p ∨ p U q.
Proof. now firstorder. Qed.

Definition F p q := □ (p ⇒ □ q).

Theorem Dummett p : F (F p p) p ⟹ (◇ □ p ⇒ □ p).
Proof.
  unfold F.
  unfold always, eventually.
  repeat intro; firstorder.
  apply NNPP; intro.
  apply not_or_and in H0.
  destruct H0.
  apply H0; intro; clear H0.
  apply not_all_ex_not in H1.
  destruct H2, H0.
  specialize (H x H0).
  inv H.
  - apply H3; clear H3; intros.
    right; intros.
    apply H2; lia.
  - destruct H1.
    apply H; clear H; intros.
    apply H3; clear H2 H3.
Abort.

End StreamLTLW.

Module StreamLTL (S : StreamType) <: LinearTemporalLogic.

Include StreamLTLW S.

Definition release        : t -> t -> t := fun x _ => x.
Definition strong_release : t -> t -> t := fun x _ => x.

Notation "p 'R' q" := (release p q)        (at level 79, right associativity) : ltl_scope.
Notation "p 'M' q" := (strong_release p q) (at level 79, right associativity) : ltl_scope.

Program Instance release_respects_implies :
  Proper (implies ==> implies ==> implies) release.
Next Obligation. now firstorder. Qed.

Program Instance strong_release_respects_implies :
  Proper (implies ==> implies ==> implies) strong_release.
Next Obligation. now firstorder. Qed.

Theorem release_def p q : p R q ≈ ¬(¬p U ¬q).
Admitted.

Theorem strong_release_def p q : p M q ≈ q U (p ∧ q).
Admitted.

End StreamLTL.
