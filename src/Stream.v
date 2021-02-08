Require Import
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.SetoidClass
  Coq.Arith.PeanoNat
  Coq.Program.Basics
  Coq.Sets.Ensembles
  Same_set.

Section Stream.

Variable a : Type.

CoInductive Stream := Cons : a -> Stream -> Stream.

CoInductive stream_eq : Stream -> Stream -> Prop :=
  | Stream_eq : forall h t1 t2,
      stream_eq t1 t2 -> stream_eq (Cons h t1) (Cons h t2).

Definition frob (s : Stream) : Stream :=
  match s with Cons h t => Cons h t end.

Theorem frob_eq : forall (s : Stream), s = frob s.
  destruct s; reflexivity.
Qed.

Definition head (s : Stream) : a :=
  match s with Cons x _ => x end.

Fixpoint from (i : nat) (s : Stream) : Stream :=
  match i with
  | O => s
  | S n =>
    match s with Cons _ xs => from n xs end
  end.

Definition tail : Stream -> Stream := from 1.
Arguments tail s /.

Lemma from_cons i x s : from (S i) (Cons x s) = from i s.
Proof. now induction i. Qed.

Lemma tail_from_1 s : tail s = from 1 s.
Proof. reflexivity. Qed.

Lemma tail_from_S i s : tail (from i s) = from (S i) s.
Proof.
  revert s.
  induction i; intros; auto.
  destruct s; auto.
  rewrite from_cons.
  rewrite IHi.
  now rewrite from_cons.
Qed.

Lemma from_tail_S i s : from i (tail s) = from (S i) s.
Proof.
  revert s.
  induction i; intros; destruct s; auto.
Qed.

Lemma from_tail i s : from i (tail s) = tail (from i s).
Proof.
  revert s.
  induction i; intros; destruct s; auto.
  now rewrite tail_from_S, from_tail_S.
Qed.

Lemma tail_from i s : tail (from i s) = from i (tail s).
Proof. symmetry. now apply from_tail. Qed.

Lemma from_S i j s : from i (from (S j) s) = from (S i) (from j s).
Proof. now rewrite <- !from_tail_S, !from_tail. Qed.

Lemma from_from i j s : from i (from j s) = from j (from i s).
Proof.
  generalize dependent j.
  induction i; intros; auto.
  specialize (IHi (S j)).
  rewrite from_S.
  rewrite <- IHi.
  now rewrite from_S.
Qed.

Lemma from_plus i j s : from i (from j s) = from (i + j) s.
Proof.
  generalize dependent j.
  induction i; intros; auto.
  rewrite PeanoNat.Nat.add_succ_comm.
  rewrite <- IHi.
  now rewrite from_S.
Qed.

Notation "( s , n ) ⊨ P" := (P (from n s)) (at level 100).

Definition every (P : Stream -> Prop) (s : Stream) := forall i, (s, i) ⊨ P.
Definition any   (P : Stream -> Prop) (s : Stream) := exists i, (s, i) ⊨ P.

Section stream_eq_coind.
  Variable R : Stream -> Stream -> Prop.

  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> head s1 = head s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tail s1) (tail s2).

  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
    cofix stream_eq_coind; destruct s1; destruct s2; intro.
    generalize (Cons_case_hd _ _ H); intro Heq; simpl in Heq; rewrite Heq.
    constructor.
    apply stream_eq_coind.
    apply (Cons_case_tl _ _ H).
  Qed.
End stream_eq_coind.

Global Program Instance stream_eq_Equivalence : Equivalence stream_eq.
Next Obligation.
  repeat intro.
  apply stream_eq_coind with (R:=fun s1 s2 => s1 = s2); intros; subst; auto.
Qed.
Next Obligation.
  repeat intro.
  eapply stream_eq_coind
    with (R := fun s1 s2 => stream_eq s2 s1); eauto; clear;
    intros s1 s2 H0.
  destruct H0; simpl; symmetry; auto.
  destruct H0; simpl; auto.
Qed.
Next Obligation.
  repeat intro.
  eapply stream_eq_coind
    with (R := fun s1 s2 => exists s3, stream_eq s1 s3 /\ stream_eq s3 s2);
    eauto; clear; intros ? ? [s3 [H0 H1] ].
  - destruct H0; inversion H1; subst; simpl; etransitivity; eauto.
  - destruct H0; inversion H1; subst; simpl; eexists; eauto.
Qed.

Global Instance Stream_Setoid `{Setoid a} : Setoid Stream := {
  equiv := stream_eq;
  setoid_equiv := stream_eq_Equivalence
}.

Global Program Instance Cons_Proper :
  Proper (eq ==> stream_eq ==> stream_eq) Cons.
Next Obligation.
  repeat intro.
  subst.
  now constructor.
Qed.

Global Program Instance head_Proper :
  Proper (stream_eq ==> eq) head.
Next Obligation.
  unfold head.
  repeat intro.
  destruct x, y.
  inversion H; subst.
  reflexivity.
Qed.

Global Program Instance tail_Proper :
  Proper (stream_eq ==> stream_eq) tail.
Next Obligation.
  unfold tail.
  repeat intro.
  destruct x, y.
  inversion H; subst.
  assumption.
Qed.

Global Program Instance from_Proper :
  Proper (@eq nat ==> stream_eq ==> stream_eq) from.
Next Obligation.
  repeat intro; subst.
  induction y; auto.
  now rewrite <- !from_tail_S, !from_tail, IHy.
Qed.

Global Program Instance any_Proper f :
  Proper (stream_eq ==> impl) f ->
  Proper (stream_eq ==> impl) (any f).
Next Obligation.
  unfold any.
  repeat intro; subst.
  destruct H1.
  exists x0.
  now rewrite <- H0.
Qed.

Global Program Instance any_flip_Proper f :
  Proper (stream_eq ==> flip impl) f ->
  Proper (stream_eq ==> flip impl) (any f).
Next Obligation.
  unfold any.
  repeat intro; subst.
  destruct H1.
  exists x0.
  now rewrite H0.
Qed.

Global Program Instance any_Same_set_Proper :
  Proper (Same_set Stream ==> Same_set Stream) any.
Next Obligation.
  unfold any.
  split; repeat intro; unfold In in *.
  - destruct H0.
    exists x1.
    now apply H.
  - destruct H0.
    exists x1.
    now apply H.
Qed.

Global Program Instance every_Proper f :
  Proper (stream_eq ==> impl) f ->
  Proper (stream_eq ==> impl) (every f).
Next Obligation.
  unfold every.
  repeat intro; subst.
  now rewrite <- H0.
Qed.

Global Program Instance every_flip_Proper f :
  Proper (stream_eq ==> flip impl) f ->
  Proper (stream_eq ==> flip impl) (every f).
Next Obligation.
  unfold every.
  repeat intro; subst.
  now rewrite H0.
Qed.

Global Program Instance every_Same_set_Proper :
  Proper (Same_set Stream ==> Same_set Stream) every.
Next Obligation.
  unfold every.
  split; repeat intro; unfold In in *.
  - now apply H; unfold In.
  - now apply H; unfold In.
Qed.

Lemma cons_inj x s y u : Cons x s = Cons y u -> x = y /\ s = u.
Proof.
  intros.
  split; inversion H; subst; auto.
Qed.

Lemma head_cons x s : head (Cons x s) = x.
Proof. now unfold head. Qed.

Lemma tail_cons x s : tail (Cons x s) = s.
Proof. now unfold tail. Qed.

Lemma cons_head_tail s : Cons (head s) (tail s) = s.
Proof.
  unfold head, tail.
  now destruct s.
Qed.

Section stream_eq_onequant.
  Variables B : Type.

  Variables f g : B -> Stream.

  Hypothesis Cons_case_hd : forall x, head (f x) = head (g x).
  Hypothesis Cons_case_tl : forall x,
    exists y, tail (f x) = f y /\ tail (g x) = g y.

  Theorem stream_eq_onequant : forall x, stream_eq (f x) (g x).
    intro.
    apply (stream_eq_coind (fun s1 s2 => exists x, s1 = f x /\ s2 = g x));
    firstorder; subst; auto.
    now exists x.
  Qed.
End stream_eq_onequant.

End Stream.

Arguments Cons {a} x s.
Arguments head {a} s.
Arguments from {a} i s.
Arguments tail {a} s.
Arguments every {a} P s.
Arguments any {a} P s.

Notation "( s , n ) ⊨ P" := (P (from n s)) (at level 10).
