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

Section LTL.

Variable a : Type.

Definition LTL := Ensemble (Stream a).

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

Variables φ ψ χ ρ : LTL.

Set Nested Proofs Allowed.

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

Lemma law_1 : ¬(⊤) ≈ ⊥.
Proof. now solve. Qed.
Lemma law_2 : ¬(⊥) ≈ ⊤.
Proof. now solve. Qed.
Lemma law_3 : ¬¬ φ ≈ φ.
Proof. now solve. Qed.
Lemma law_4 : (φ ≈ ψ) -> ¬ φ ≈ ¬ ψ.
Proof. intro; now rewrite H. Qed.
Lemma law_5 : φ ∨ (ψ ∨ χ) ≈ (φ ∨ ψ) ∨ χ.
Proof. now solve. Qed.
Lemma law_6 : φ ∨ ψ ≈ ψ ∨ φ.
Proof. now solve. Qed.
Lemma law_7 : φ ∨ (⊥) ≈ φ.
Proof. now solve. Qed.
Lemma law_8 : φ ∧ ψ ≈ ψ ∧ φ.
Proof. now solve. Qed.
Lemma law_9 : φ ∧ (ψ ∧ χ) ≈ (φ ∧ ψ) ∧ χ.
Proof. now solve. Qed.
Lemma law_10 : φ ∧ (⊤) ≈ φ.
Proof. now solve. Qed.
Lemma law_11 : φ ∨ (ψ ∧ χ) ≈ (φ ∨ ψ) ∧ (φ ∨ χ).
Proof. now solve. Qed.
Lemma law_12 : φ ∧ (ψ ∨ χ) ≈ (φ ∧ ψ) ∨ (φ ∧ χ).
Proof. now solve. Qed.
Lemma law_13 : ¬(φ ∨ ψ) ≈ ¬ φ ∧ ¬ ψ.
Proof. now solve. Qed.
Lemma law_14 : ¬(φ ∧ ψ) ≈ ¬ φ ∨ ¬ ψ.
Proof. now solve. Qed.

Lemma law_15 : ◯ (⊤) ≈ ⊤.
Proof. now solve. Qed.
Lemma law_16 : ◯ (⊥) ≈ ⊥.
Proof. now solve. Qed.
Lemma law_17 : ◯ φ ≈ ¬◯¬ φ.
Proof. solve. now apply NNPP. Qed.
Lemma law_18 : ◇ (⊤) ≈ ⊤.
Proof. solve; now exists 0; constructor. Qed.
Lemma law_19 : ◇ (⊥) ≈ ⊥.
Proof. now solve. Qed.
Lemma law_20 : □ (⊤) ≈ ⊤.
Proof. now solve. Qed.
Lemma law_21 : □ (⊥) ≈ ⊥.
Proof. now solve. Qed.
Lemma law_22 : ¬◯ φ ≈ ◯¬ φ.
Proof. now solve. Qed.
Lemma law_23 : ¬□ φ ≈ ◇¬ φ.
Proof. now solve. Qed.
Lemma law_24 : ¬◇ φ ≈ □¬ φ.
Proof. now solve. Qed.
Lemma law_25 : ¬◇□ φ ≈ □◇¬ φ.
Proof. now solve. Qed.
Lemma law_26 : ¬□◇ φ ≈ ◇□¬ φ.
Proof. now solve. Qed.
Lemma law_27 : forall s, □ φ s -> φ s.
Proof. now solve. Qed.
Lemma law_28 : forall s, φ s -> ◇ φ s.
Proof. now solve. Qed.
Lemma law_29 : forall s, □ φ s -> ◯ φ s.
Proof. now solve. Qed.
Lemma law_30 : forall s, □ φ s -> ◯□ φ s.
Proof. now solve. Qed.
Lemma law_31 : forall s, □ φ s -> □◯ φ s.
Proof. now solve. Qed.
Lemma law_32 : forall s, ◯ φ s -> ◇ φ s.
Proof. now solve. Qed.
Lemma law_33 : forall s, □ φ s -> ◇ φ s.
Proof. now solve. Qed.
Lemma law_34 : forall s, ◇□ φ s -> □◇ φ s.
Proof. now solve. Qed.
Lemma law_35 : forall s, □¬ φ s -> ¬□ φ s.
Proof. now solve. Qed.

Lemma law_36 : □□ φ ≈ □ φ.
Proof. now solve. Qed.
Lemma law_37 : ◇◇ φ ≈ ◇ φ.
Proof. now solve. Qed.
Lemma law_38 : □◯ φ ≈ ◯□ φ.
Proof. now solve. Qed.
Lemma law_39 : ◇◯ φ ≈ ◯◇ φ.
Proof. now solve. Qed.
Lemma law_40 : □ φ ≈ φ ∧ ◯□ φ.
Proof.
  solve.
  generalize dependent x.
  induction i; auto; simpl.
  now intros; intuition.
Qed.
Lemma law_41 : □ φ ≈ φ ∧ ◯ φ ∧ ◯□ φ.
Proof.
  solve.
  generalize dependent x.
  induction i; auto; simpl.
  now intros; intuition.
Qed.
Lemma law_42 : ◇ φ ≈ φ ∨ ◯◇ φ.
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
Lemma law_43 : ◇□◇ φ ≈ □◇ φ.
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
Lemma law_44 : □◇□ φ ≈ ◇□ φ.
Proof. Fail now solve. Abort.
Lemma law_45 : □◇□◇ φ ≈ □◇ φ.
Proof. Fail now solve. Abort.
Lemma law_46 : ◇□◇□ φ ≈ ◇□ φ.
Proof. Fail now solve. Abort.
Lemma law_47 : ◯□◇ φ ≈ □◇ φ.
Proof. Fail now solve. Abort.
Lemma law_48 : ◯◇□ φ ≈ ◇□ φ.
Proof. Fail now solve. Abort.

Lemma law_49 : ◯ (φ → ψ) ≈ ◯ φ → ◯ ψ.
Proof. solve. Qed.
Lemma law_50 : ◯ (φ ∧ ψ) ≈ ◯ φ ∧ ◯ ψ.
Proof. now solve. Qed.
Lemma law_51 : ◯ (φ ∨ ψ) ≈ ◯ φ ∨ ◯ ψ.
Proof. now solve. Qed.
Lemma law_52 : ◯ (φ ↔ ψ) ≈ ◯ φ ↔ ◯ ψ.
Proof. now solve. Qed.
Lemma law_53 : □ (φ ∧ ψ) ≈ □ φ ∧ □ ψ.
Proof.
  solve;
  specialize (H i);
  now solve.
Qed.
Lemma law_54 : □ (φ ∨ ψ) ≉ □ φ ∨ □ ψ.
Proof. Fail now solve. Abort.   (* appears unsolvable *)
Lemma law_55 : φ ∨ ◇ φ ≈ ◇ φ.
Proof.
  solve.
  - now right; exists x0.
Qed.
Lemma law_56 : ◇ φ ∧ φ ≈ φ.
Proof. now solve. Qed.
Lemma law_57 : ◇ (φ ∧ ψ) ≉ ◇ φ ∧ ◇ ψ.
Proof. Fail now solve. Abort.   (* appears unsolvable *)
Lemma law_58 : ◇ (φ ∨ ψ) ≉ ◇ φ ∨ ◇ ψ.
Proof. Fail now solve. Abort.   (* appears unsolvable *)
Lemma law_59 : φ ∧ □ φ ≈ □ φ.
Proof. now solve. Qed.
Lemma law_60 : □ φ ∨ φ ≈ φ.
Proof. now solve. Qed.
Lemma law_61 : ◇ φ ∧ □ φ ≈ □ φ.
Proof. now solve. Qed.
Lemma law_62 : □ φ ∨ ◇ φ ≈ ◇ φ.
Proof.
  solve.
  now right; exists x0.
Qed.
Lemma law_63 : ◇□ (φ ∧ ψ) ≈ ◇□ φ ∧ ◇□ ψ.
Proof.
  solve.
  - exists x0; intros.
    now destruct (H i).
  - exists x0; intros.
    now destruct (H i).
  - admit.
Abort.
Lemma law_64 : □◇ (φ ∨ ψ) ≈ □◇ φ ∨ □◇ ψ.
Proof. solve. Abort.
Lemma law_65 : ◇□ (φ → □ ψ) ≈ ◇□¬ φ ∧ ◇□ ψ.
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
Lemma law_66 : □ (□◇ φ → ◇ ψ) ≈ ◇□¬ φ ∧ □◇ ψ.
Proof. Fail now solve. Abort.
Lemma law_67 : □ ((φ ∨ □ ψ) ∧ (□ φ ∨ ψ)) ≈ □ φ ∨ □ ψ.
Proof. Fail now solve. Abort.
Lemma law_68 : ◇ φ ≈ ¬□¬ φ.
Proof. now solve. Qed.
Lemma law_69 : □ φ ≈ ¬◇¬ φ.
Proof.
  solve.
  specialize (H i); simpl in H.
  unfold Complement, In, not in H.
  now apply NNPP in H.
Qed.
Lemma law_70 : ◇ φ ∧ □¬ φ ≈ ⊥.
Proof. now solve. Qed.
Lemma law_71 : □ φ ∧ ◇¬ φ ≈ ⊥.
Proof. now solve. Qed.
Lemma law_72 : □ φ ∧ □¬ φ ≈ ⊥.
Proof. now solve. Qed.
Lemma law_73 : □◇ φ ∧ ◇□¬ φ ≈ ⊥.
Proof. now solve. Qed.
Lemma law_74 : ◇□ φ ∧ □◇¬ φ ≈ ⊥.
Proof. now solve. Qed.
Lemma law_75 : ◇□ φ ∧ ◇□¬ φ ≈ ⊥.
Proof. Fail now solve. Abort.
Lemma law_76 : forall s, (◇ φ ∨ □¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_77 : forall s, (□ φ ∨ ◇¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_78 : forall s, (◇ φ ∨ ◇¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_79 : forall s, (□◇ φ ∨ ◇□¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_80 : forall s, (□◇ φ ∨ □◇¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_81 : forall s, (◇□ φ ∨ □◇¬ φ) s.
Proof. Fail now solve. Abort.
Lemma law_82 : forall s, ◇ (φ → ψ) s -> (□ φ → ◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_83 : forall s, (φ → □ φ) s -> (φ → ◯□ φ) s.
Proof. Fail now solve. Abort.
Lemma law_84 : forall s, (φ ∧ ◇¬ φ) s -> (◇ (φ ∧ ◯¬ φ)) s.
Proof. Fail now solve. Abort.
Lemma law_85 : forall s, □ (φ → ψ) s -> (□ φ → □ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_86 : forall s, (□ φ ∨ □ ψ) s -> □ (φ ∨ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_87 : forall s, (□ φ ∧ ◇ ψ) s -> ◇ (φ ∧ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_88 : forall s, (◇ φ → ◇ ψ) s -> ◇ (φ → ψ) s.
Proof. Fail now solve. Abort.
Lemma law_89 : forall s, ◇ (φ ∧ ψ) s -> (◇ φ ∧ ◇ ψ) s.
Proof. now solve. Qed.
Lemma law_90 : forall s, □◇ (φ ∧ ψ) s -> (□◇ φ ∧ □◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_91 : forall s, □◇ (φ ∨ ψ) s -> (□◇ φ ∨ □◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_92 : forall s, ◇□ (φ ∧ ψ) s -> (◇□ φ ∧ ◇□ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_93 : forall s, (◇□ φ ∨ ◇□ ψ) s -> ◇□ (φ ∨ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_94 : forall s, (◇□ φ ∧ □◇ ψ) s -> □◇ (φ ∧ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_95 : forall s, (◇□ φ ∧ □ (□ φ → ◇ ψ)) s -> ◇ ψ s.
Proof. Fail now solve. Abort.
Lemma law_96 : forall s, □ (φ → ψ) s -> (◯ φ → ◯ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_97 : forall s, □ (φ → ψ) s -> (◇ φ → ◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_98 : forall s, □ (φ → ψ) s -> (□◇ φ → □◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_99 : forall s, □ (φ → ψ) s -> (◇□ φ → ◇□ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_100 : forall s, □ φ s -> (◯ ψ → ◯ (φ ∧ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_101 : forall s, □ φ s -> (◇ ψ → ◇ (φ ∧ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_102 : forall s, □ φ s -> (□ ψ → □ (φ ∧ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_103 : forall s, □ φ s -> (◯ ψ → ◯ (φ ∨ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_104 : forall s, □ φ s -> (◇ ψ → ◇ (φ ∨ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_105 : forall s, □ φ s -> (□ ψ → □ (φ ∨ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_106 : forall s, □ φ s -> (◯ ψ → ◯ (φ → ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_107 : forall s, □ φ s -> (◇ ψ → ◇ (φ → ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_108 : forall s, □ φ s -> (□ ψ → □ (φ → ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_109 : forall s, □ (□ φ → ψ) s -> (□ φ → □ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_110 : forall s, □ (φ → ◇ψ) s -> (◇ φ → ◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_111 : forall s, □ (φ → ◯ φ) s -> (φ → □ φ) s.
Proof. Fail now solve. Abort.
Lemma law_112 : forall s, □ (φ → ◯ ψ) s -> (φ → ◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_113 : forall s, □ (φ → ◯¬ φ) s -> (φ → ¬□ φ) s.
Proof. Fail now solve. Abort.
Lemma law_114 : forall s, □ (◯ φ → φ) s -> (◇ φ → φ) s.
Proof. Fail now solve. Abort.
Lemma law_115 : forall s, □ (φ ∨ ◯ ψ → ψ) s -> (◇ φ → ψ) s.
Proof. Fail now solve. Abort.
Lemma law_116 : forall s, □ (φ → ◯ φ ∧ ψ) s -> (φ → □ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_117 : forall s, □ (φ → (◯ φ ∧ ψ) ∨ χ) s -> (φ → □ ψ ∨ (ψ U χ)) s.
Proof. Fail now solve. Abort.
Lemma law_118 : forall s, □ (φ → ◯ (φ ∨ ψ)) s -> (φ → □ φ ∨ (φ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_119 : forall s, □ ((φ → ψ) ∧ (ψ → ◯ χ) ∧ (χ → ρ)) s -> (φ → ◯ ρ) s.
Proof. Fail now solve. Abort.
Lemma law_120 : forall s, □ ((φ → ψ) ∧ (ψ → ◇ χ) ∧ (χ → ρ)) s -> (φ → ◇ ρ) s.
Proof. Fail now solve. Abort.
Lemma law_121 : forall s, □ ((φ → ψ) ∧ (ψ → □ χ) ∧ (χ → ρ)) s -> (φ → □ ρ) s.
Proof. Fail now solve. Abort.
Lemma law_122 : forall s, □ ((φ → ◇ ψ) ∧ (ψ → ◇ χ)) s -> (φ → ◇ χ) s.
Proof. Fail now solve. Abort.
Lemma law_123 : forall s, □ ((φ → □ ψ) ∧ (ψ → □ χ)) s -> (φ → □ χ) s.
Proof. Fail now solve. Abort.
Lemma law_124 : forall s, (□ (□ φ → ◇ ψ) ∧ (ψ → ◯ χ)) s -> (□ φ → ◯□◇ χ) s.
Proof. Fail now solve. Abort.
Lemma law_125 : forall s, □ (φ ∨ ψ) s -> exists u, □ ((φ ∧ u) ∨ (ψ ∧ ¬ u)) s.
Proof. Fail now solve. Abort.
Lemma law_126 : forall s, □ ((φ → ◇ (ψ ∨ χ)) ∧ (ψ → ◇ ρ) ∧ (χ → ◇ ρ)) s -> (φ → ◇ ρ) s.
Proof. Fail now solve. Abort.
Lemma law_127 : forall s, (□ (□ φ → ψ) ∨ □ (□ ψ → φ)) s.
Proof. Fail now solve. Abort.
Lemma law_128 : φ U (⊥) ≈ ⊥.
Proof. now solve. Qed.
Lemma law_129 : ⊥ U φ ≈ ⊥.
Proof. Fail now solve. Abort.
Lemma law_130 : φ U (⊤) ≈ ⊤.
Proof. Fail now solve. Abort.
Lemma law_131 : φ U φ ≈ φ.
Proof. Fail now solve. Abort.
Lemma law_132 : ¬ φ U φ ≈ ◇ φ.
Proof. Fail now solve. Abort.
Lemma law_133 : forall s, ψ s -> (φ U φ) s.
Proof. Fail now solve. Abort.
Lemma law_134 : forall s, (φ U ψ) s -> (φ ∨ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_135 : forall s, (φ ∧ ψ) s -> (φ U ψ) s.
Proof. Fail now solve. Abort.
Lemma law_136 : forall s, ((φ U ψ) ∨ (φ U ¬ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_137 : φ ∨ (φ U ψ) ≈ φ ∨ ψ.
Proof. Fail now solve. Abort.
Lemma law_138 : (φ U ψ) ∨ ψ ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_139 : (φ U ψ) ∧ ψ ≈ ψ.
Proof. Fail now solve. Abort.
Lemma law_140 : (φ U ψ) ∨ (φ ∧ ψ) ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_141 : (φ U ψ) ∧ (φ ∨ ψ) ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_142 : φ U (φ U ψ) ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_143 : (φ U ψ) U ψ ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_144 : φ U ψ ≈ ψ ∨ (φ ∧ ◯ (φ U ψ)).
Proof. Fail now solve. Abort.
Lemma law_145 : φ U ψ ≈ (φ ∨ ψ) U ψ.
Proof. Fail now solve. Abort.
Lemma law_146 : φ U ψ ≈ (φ ∧ ¬ ψ) U ψ.
Proof. Fail now solve. Abort.
Lemma law_147 : φ U (ψ ∨ χ) ≈ (φ U ψ) ∨ (φ U χ).
Proof. Fail now solve. Abort.
Lemma law_148 : forall s, ((φ U χ) ∨ (ψ U χ)) s -> ((φ ∨ ψ) U χ) s.
Proof. now solve. Qed.
Lemma law_149 : (φ ∧ ψ) U χ ≈ (φ U χ) ∧ (ψ U χ).
Proof. Fail now solve. Abort.
Lemma law_150 : forall s, (φ U (ψ ∧ χ)) s -> ((φ U ψ) ∧ (φ U χ)) s.
Proof. now solve. Qed.
Lemma law_151 : forall s, (φ U (ψ ∧ χ)) s -> (φ U (ψ U χ)) s.
Proof. Fail now solve. Abort.
Lemma law_152 : forall s, ((φ ∧ ψ) U χ) s -> ((φ U ψ) U χ) s.
Proof. Fail now solve. Abort.
Lemma law_153 : forall s, ((φ ∧ ψ) U χ) s -> (φ U (ψ U χ)) s.
Proof. Fail now solve. Abort.
Lemma law_154 : ◯ (φ U ψ) ≈ (◯ φ) U (◯ ψ).
Proof. Fail now solve. Abort.
Lemma law_155 : ◇ (φ U ψ) ≉ (◇ φ) U (◇ ψ).
Proof. Fail now solve. Abort.
Lemma law_156 : ◇ φ ≈ ⊤ U φ.
Proof. Fail now solve. Abort.
Lemma law_157 : (φ U ψ) ∧ ◇ ψ ≈ φ U ψ.
Proof. now solve. Qed.
Lemma law_158 : (φ U ψ) ∨ ◇ ψ ≈ ◇ ψ.
Proof. Fail now solve. Abort.
Lemma law_159 : φ U ◇ ψ ≈ ◇ ψ.
Proof. Fail now solve. Abort.
Lemma law_160 : φ U □ φ ≈ □ φ.
Proof. Fail now solve. Abort.
Lemma law_161 : φ U □ ψ ≈ □ (φ U ψ).
Proof. Fail now solve. Abort.
Lemma law_162 : forall s, (◇ φ → ((φ → ψ) U φ)) s.
Proof. Fail now solve. Abort.
Lemma law_163 : forall s, ((φ U ψ) ∧ (¬ ψ U χ)) s -> (φ U χ) s.
Proof. Fail now solve. Abort.
Lemma law_164 : forall s, (φ U (ψ U χ)) s -> ((φ ∨ ψ) U χ) s.
Proof. Fail now solve. Abort.
Lemma law_165 : forall s, ((φ → ψ) U χ) s -> ((φ U χ) → (ψ U χ)) s.
Proof. Fail now solve. Abort.
Lemma law_166 : forall s, ((¬ φ U (ψ U χ)) ∧ (φ U χ)) s -> (ψ U χ) s.
Proof. Fail now solve. Abort.
Lemma law_167 : forall s, ((φ U (¬ ψ U χ)) ∧ (ψ U χ)) s -> (φ U χ) s.
Proof. Fail now solve. Abort.
Lemma law_168 : forall s, ((φ U ψ) ∧ (¬ ψ U φ)) s -> φ s.
Proof. Fail now solve. Abort.
Lemma law_169 : forall s, (φ ∧ (¬ φ U ψ)) s -> ψ s.
Proof. Fail now solve. Abort.
Lemma law_170 : forall s, □ φ s -> (◯ ψ → ◯ (φ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_171 : forall s, □ φ s -> (◇ ψ → ◇ (φ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_172 : forall s, □ φ s -> (□ ψ → □ (φ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_173 : forall s, □ φ s -> ¬(ψ U ¬ φ) s.
Proof. now solve. Qed.
Lemma law_174 : forall s, □ φ s -> (◇ ψ) s -> (φ U ψ) s.
Proof. now solve. Qed.
Lemma law_175 : forall s, (□ φ ∧ (ψ U χ)) s -> ((φ ∧ ψ) U (φ ∧ χ)) s.
Proof. Fail now solve. Abort.
Lemma law_176 : forall s, □ (φ → ψ) s -> ((χ U φ) → (χ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_177 : forall s, □ (φ → ψ) s -> ((φ U χ) → (ψ U χ)) s.
Proof. Fail now solve. Abort.
Lemma law_178 : forall s, (φ U ψ) s -> (◇ ψ) s.
Proof. now solve. Qed.
Lemma law_179 : forall s, □ ((φ → ψ U χ) ∧ (χ → ψ U ρ)) s -> (φ → □ χ) s.
Proof. Fail now solve. Abort.
Lemma law_180 : forall s, □ ((φ → χ) ∧ (ψ → ρ)) s -> (φ U ψ → χ U ρ) s.
Proof. Fail now solve. Abort.
Lemma law_181 : forall s, □ (φ → ¬ ψ ∧ ◯ χ) s -> (φ → ¬(ψ U χ)) s.
Proof. Fail now solve. Abort.

Lemma law_182 : φ W φ ≈ φ.
Proof. Fail now solve. Abort.
Lemma law_183 : φ W ψ ≈ (φ U ψ) ∨ □ φ.
Proof. now solve. Qed.
Lemma law_184 : ¬(φ W ψ) ≈ ¬ ψ U (¬ φ ∧ ¬ ψ).
Proof. Fail now solve. Abort.
Lemma law_185 : ¬(φ W ψ) ≈ (φ ∧ ¬ ψ) U (¬ φ ∧ ¬ ψ).
Proof. Fail now solve. Abort.
Lemma law_186 : ¬(φ U ψ) ≈ ¬ ψ W (¬ φ ∧ ¬ ψ).
Proof. Fail now solve. Abort.
Lemma law_187 : ¬(φ U ψ) ≈ (φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ).
Proof. Fail now solve. Abort.
Lemma law_188 : ¬(¬ φ U ¬ ψ) ≈ ψ W (φ ∧ ψ).
Proof. Fail now solve. Abort.
Lemma law_189 : ¬(¬ φ U ¬ ψ) ≈ (¬ φ ∧ ψ) W (φ ∧ ψ).
Proof. Fail now solve. Abort.
Lemma law_190 : ¬(¬ φ W ¬ ψ) ≈ ψ U (φ ∧ ψ).
Proof. Fail now solve. Abort.
Lemma law_191 : ¬(¬ φ W ¬ ψ) ≈ (¬ φ ∧ ψ) U (φ ∧ ψ).
Proof. Fail now solve. Abort.
Lemma law_192 : φ W ψ ≈ φ U (ψ ∨ □ φ).
Proof. Fail now solve. Abort.
Lemma law_193 : φ W ψ ≈ (φ ∨ ψ) W ψ.
Proof. Fail now solve. Abort.
Lemma law_194 : φ W ψ ≈ □ (φ ∧ ¬ ψ) ∨ (φ U ψ).
Proof. Fail now solve. Abort.
Lemma law_195 : φ U ψ ≈ (φ W ψ) ∧ ◇ ψ.
Proof. Fail now solve. Abort.
Lemma law_196 : φ U ψ ≈ (φ W ψ) ∧ ¬□¬ ψ.
Proof. Fail now solve. Abort.
Lemma law_197 : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof. Fail now solve. Abort.
Lemma law_198 : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).
Proof. Fail now solve. Abort.
Lemma law_199 : φ W ψ ≈ (φ ∧ ¬ ψ) W ψ.
Proof. Fail now solve. Abort.
Lemma law_200 : φ W (φ W ψ) ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_201 : (φ W ψ) W ψ ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_202 : φ W (φ U ψ) ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_203 : (φ U ψ) W ψ ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_204 : φ U (φ W ψ) ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_205 : (φ W ψ) U ψ ≈ φ U ψ.
Proof. Fail now solve. Abort.
Lemma law_206 : ◯ (φ W ψ) ≈ ◯ φ W ◯ ψ.
Proof. Fail now solve. Abort.
Lemma law_207 : φ W ◇ ψ ≈ □ φ ∨ ◇ ψ.
Proof. Fail now solve. Abort.
Lemma law_208 : ◇ φ W φ ≈ ◇ φ.
Proof. Fail now solve. Abort.
Lemma law_209 : □ φ ∧ (φ W ψ) ≈ □ φ.
Proof. now solve. Qed.
Lemma law_210 : □ φ ∨ (φ W ψ) ≈ φ W ψ.
Proof. now solve. Qed.
Lemma law_211 : φ W □ φ ≈ □ φ.
Proof. Fail now solve. Abort.
Lemma law_212 : □ φ ≈ φ W ⊥.
Proof. now solve. Qed.
Lemma law_213 : ◇ φ ≈ ¬(¬ φ W ⊥).
Proof. now solve. Qed.
Lemma law_214 : ⊤ W φ ≈ ⊤.
Proof. now solve. Qed.
Lemma law_215 : φ W (⊤) ≈ ⊤.
Proof. Fail now solve. Abort.
Lemma law_216 : ⊥ W φ ≈ φ.
Proof. Fail now solve. Abort.
Lemma law_217 : φ W (ψ ∨ χ) ≈ (φ W ψ) ∨ (φ W χ).
Proof. Fail now solve. Abort.
Lemma law_218 : (φ ∧ ψ) W χ ≈ (φ W χ) ∧ (ψ W χ).
Proof. Fail now solve. Abort.
Lemma law_219 : φ ∨ (φ W ψ) ≈ φ ∨ ψ.
Proof. Fail now solve. Abort.
Lemma law_220 : (φ W ψ) ∨ ψ ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_221 : (φ W ψ) ∧ ψ ≈ ψ.
Proof. Fail now solve. Abort.
Lemma law_222 : (φ W ψ) ∧ (φ ∨ ψ) ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_223 : (φ W ψ) ∨ (φ ∧ ψ) ≈ φ W ψ.
Proof. Fail now solve. Abort.
Lemma law_224 : ((¬ φ U ψ) ∨ (¬ ψ U φ)) ≈ ◇ (φ ∨ ψ).
Proof. Fail now solve. Abort.
Lemma law_225 : forall s, ψ s -> (φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_226 : forall s, (φ W φ) s -> (φ ∨ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_227 : forall s, (φ W φ) s -> (□ φ ∨ ◇ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_228 : forall s, (¬ φ W φ) s.
Proof. Fail now solve. Abort.
Lemma law_229 : forall s, ((φ → ψ) W φ) s.
Proof. Fail now solve. Abort.
Lemma law_230 : forall s, ((φ W ψ) ∨ (φ W ¬ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_231 : forall s, (φ W (ψ ∧ χ)) s -> ((φ W ψ) ∧ (φ W χ)) s.
Proof. Fail now solve. Abort.
Lemma law_232 : forall s, ((φ W χ) ∨ (ψ W χ)) s -> ((φ ∨ ψ) W χ) s.
Proof. Fail now solve. Abort.
Lemma law_233 : forall s, (φ U ψ) s -> (φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_234 : forall s, (φ W □ ψ) s -> □ (φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_235 : forall s, ¬(φ U ψ) s -> ((φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_236 : forall s, ¬(φ W ψ) s -> ((φ ∧ ¬ ψ) U (¬ φ ∧ ¬ ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_237 : forall s, ((φ → ψ) W χ) s -> ((φ W χ) → (ψ W χ)) s.
Proof. Fail now solve. Abort.
Lemma law_238 : forall s, □ φ s -> (φ W ψ) s.
Proof. now solve. Qed.
Lemma law_239 : forall s, □ φ s -> (◯ ψ → ◯ (φ W ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_240 : forall s, □ φ s -> (◇ ψ → ◇ (φ W ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_241 : forall s, □ φ s -> (□ ψ → □ (φ W ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_242 : forall s, □ (φ ∨ ψ) s -> (φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_243 : forall s, □ (¬ ψ → φ) s -> (φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_244 : forall s, □ (φ → (◯ φ ∧ ψ) ∨ χ) s -> (φ → ψ W χ) s.
Proof. Fail now solve. Abort.
Lemma law_245 : forall s, □ (φ → ◯ (φ ∨ ψ)) s -> (φ → φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_246 : forall s, □ (φ → ◯ φ) s -> (φ → φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_247 : forall s, □ (φ → ψ ∧ ◯ φ) s -> (φ → φ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_248 : forall s, (□ φ ∧ (ψ W χ)) s -> ((φ ∧ ψ) W (φ ∧ χ)) s.
Proof. Fail now solve. Abort.
Lemma law_249 : forall s, ((φ W ψ) ∧ □¬ ψ) s -> □ φ s.
Proof. now solve. Qed.
Lemma law_250 : forall s, □ φ s -> ((φ U ψ) ∨ □¬ ψ) s.
Proof. Fail now solve. Abort.
Lemma law_251 : forall s, (¬□ φ ∧ (φ W ψ)) s -> ◇ ψ s.
Proof. now solve. Qed.
Lemma law_252 : forall s, ◇ ψ s -> (¬□ φ ∨ (φ U ψ)) s.
Proof. Fail now solve. Abort.
Lemma law_253 : forall s, □ (φ → ψ) s -> (φ W χ → ψ W χ) s.
Proof. Fail now solve. Abort.
Lemma law_254 : forall s, □ (φ → ψ) s -> (χ W φ → χ W ψ) s.
Proof. Fail now solve. Abort.
Lemma law_255 : forall s, □ ((φ → χ) ∧ (ψ → ρ)) s -> ((φ W ψ) → (χ W ρ)) s.
Proof. Fail now solve. Abort.
Lemma law_256 : forall s, □ ((φ → ψ W χ) ∧ (χ → ψ W ρ)) s -> (φ → ψ W ρ) s.
Proof. Fail now solve. Abort.
Lemma law_257 : forall s, ((φ U ψ) W χ) s -> ((φ W ψ) W χ) s.
Proof. Fail now solve. Abort.
Lemma law_258 : forall s, (φ W (ψ U χ)) s -> (φ W (ψ W χ)) s.
Proof. Fail now solve. Abort.
Lemma law_259 : forall s, (φ U (ψ U χ)) s -> (φ U (ψ W χ)) s.
Proof. Fail now solve. Abort.
Lemma law_260 : forall s, ((φ U ψ) U χ) s -> ((φ W ψ) U χ) s.
Proof. Fail now solve. Abort.
Lemma law_261 : forall s, ((φ U ψ) U χ) s -> ((φ ∨ ψ) U χ) s.
Proof. Fail now solve. Abort.
Lemma law_262 : forall s, ((φ W ψ) W χ) s -> ((φ ∨ ψ) W χ) s.
Proof. Fail now solve. Abort.
Lemma law_263 : forall s, (φ W (ψ W χ)) s -> (φ W (ψ ∨ χ)) s.
Proof. Fail now solve. Abort.
Lemma law_264 : forall s, (φ W (ψ W χ)) s -> ((φ ∨ ψ) W χ) s.
Proof. Fail now solve. Abort.
Lemma law_265 : forall s, (φ W (ψ ∧ χ)) s -> ((φ W ψ) W χ) s.
Proof. Fail now solve. Abort.
Lemma law_266 : forall s, ((¬ φ W ψ) ∨ (¬ ψ W φ)) s.
Proof. Fail now solve. Abort.
Lemma law_267 : forall s, ((φ W ψ) ∧ (¬ ψ W χ)) s -> (φ W χ) s.
Proof. Fail now solve. Abort.

Lemma law_268 : φ R ψ ≈ ¬(¬ φ U ¬ ψ).
Proof. now solve. Qed.
Lemma law_269 : φ U ψ ≈ ¬(¬ φ R ¬ ψ).
Proof. now solve. Qed.
Lemma law_270 : φ W ψ ≈ ψ R (ψ ∨ φ).
Proof. Fail now solve. Abort.
Lemma law_271 : φ R ψ ≈ ψ W (ψ ∧ φ).
Proof. Fail now solve. Abort.
Lemma law_272 : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).
Proof. Fail now solve. Abort.
Lemma law_273 : φ R (ψ ∨ χ) ≈ (φ R ψ) ∨ (φ R χ). (* ??? *)
Proof. Fail now solve. Abort.
Lemma law_274 : (φ ∧ ψ) R χ ≈ (φ R χ) ∧ (ψ R χ). (* ??? *)
Proof. Fail now solve. Abort.
Lemma law_275 : ◯ (φ R ψ) ≈ (◯ φ) R (◯ ψ).
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
Lemma law_276 : □ ψ ≈ ⊥ R ψ.
Proof. Fail now solve. Abort.

Lemma law_277 : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Proof. now solve. Qed.
Lemma law_278 : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Proof. Fail now solve. Abort.
Lemma law_279 : ¬(φ W ψ) ≈ (¬ φ M ¬ ψ).
Proof. Fail now solve. Abort.
Lemma law_280 : ¬(φ M ψ) ≈ (¬ φ W ¬ ψ).
Proof. Fail now solve. Abort.

End LTL.
