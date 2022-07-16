Require Import
  Coq.Sets.Ensembles
  Coq.Sets.Finite_sets
  Coq.Sets.Finite_sets_facts
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid
  Coq.Relations.Relation_Definitions.

#[global]
Program Instance Same_set_Equivalence {A} : Equivalence (@Same_set A).
Obligation 1.
  intro x.
  constructor; intros y H; exact H.
Qed.
Obligation 2.
  intros x y H.
  destruct H.
  split; trivial.
Qed.
Obligation 3.
  intros x y z H1 H2.
  destruct H1, H2.
  split; trivial.
    intros w H3.
    apply H1.
    apply H.
    exact H3.
  intros w H3.
  apply H0.
  apply H2.
  exact H3.
Qed.

Add Parametric Relation {A : Type} : (Ensemble A) (Same_set A)
  reflexivity  proved by (@Equivalence_Reflexive  _ _ Same_set_Equivalence)
  symmetry     proved by (@Equivalence_Symmetric  _ _ Same_set_Equivalence)
  transitivity proved by (@Equivalence_Transitive _ _ Same_set_Equivalence)
  as Same_set_relation.

Add Parametric Morphism A : (Same_set A)
  with signature (Same_set A ==> Same_set A ==> Basics.impl)
    as Same_set_equiv.
Proof.
  unfold Basics.impl; intros.
  destruct H, H0, H1.
  split; intros z H5.
    apply H0, H1, H2, H5.
  apply H, H4, H3, H5.
Qed.

Add Parametric Morphism A : (Same_set A)
  with signature (Same_set A ==> Same_set A ==> Basics.flip Basics.impl)
    as Same_set_equiv'.
Proof.
  unfold Basics.impl; intros.
  destruct H, H0, H1.
  split; intros z H5.
    apply H3, H1, H, H5.
  apply H2, H4, H0, H5.
Qed.

Add Parametric Morphism A : (Singleton A)
  with signature (eq ==> Same_set A)
    as Singleton_Same_set.
Proof. intros; reflexivity. Qed.

Add Parametric Morphism A : (In A)
  with signature (Same_set A ==> Same_set A)
    as In_Same_set.
Proof.
  intros.
  exact H.
Qed.

Add Parametric Morphism A : (In A)
  with signature (Same_set A ==> eq ==> Basics.impl)
    as In_Same_set_eq.
Proof.
  unfold Basics.impl; intros; subst.
  destruct H.
  apply H, H0.
Qed.

Add Parametric Morphism A : (In A)
  with signature (Same_set A ==> eq ==> Basics.flip Basics.impl)
    as In_Same_set_eq'.
Proof.
  unfold Basics.impl; intros; subst.
  destruct H.
  apply H1, H0.
Qed.

Add Parametric Morphism A : (In A)
  with signature (Same_set A --> eq ==> Basics.impl)
    as In_Same_set_eq''.
Proof.
  unfold Basics.impl; intros; subst.
  destruct H.
  apply H1, H0.
Qed.

Add Parametric Morphism A : (In A)
  with signature (Same_set A --> eq ==> Basics.flip Basics.impl)
    as In_Same_set_eq'''.
Proof.
  unfold Basics.impl; intros; subst.
  destruct H.
  apply H, H0.
Qed.

Add Parametric Morphism A : (Union A)
  with signature (Same_set A ==> Same_set A ==> Same_set A)
    as Union_Same_set.
Proof.
  intros.
  destruct H, H0.
  split; intros z H3;
  inversion H3; subst; clear H3.
  - apply Union_introl.
    apply H, H4.
  - apply Union_intror.
    apply H0, H4.
  - apply Union_introl.
    apply H1, H4.
  - apply Union_intror.
    apply H2, H4.
Qed.

Add Parametric Morphism A : (Intersection A)
  with signature (Same_set A ==> Same_set A ==> Same_set A)
    as Intersection_Same_set.
Proof.
  intros.
  destruct H, H0.
  split; intros z H3;
  inversion H3; subst; clear H3;
  constructor; auto.
Qed.

Add Parametric Morphism A : (Add A)
  with signature (Same_set A ==> eq ==> Same_set A)
    as Add_Same_set.
Proof.
  unfold Add; intros.
  subst.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism A : (Setminus A)
  with signature (Same_set A ==> Same_set A ==> Same_set A)
    as Setminus_Same_set.
Proof.
  intros.
  destruct H, H0.
  split; intros z H3;
  inversion H3; subst; clear H3.
    split.
      apply H, H4.
    unfold not; intros.
    contradiction H5.
    apply H2, H3.
  split.
    apply H1, H4.
  unfold not; intros.
  contradiction H5.
  apply H0, H3.
Qed.

Add Parametric Morphism A : (Subtract A)
  with signature (Same_set A ==> eq ==> Same_set A)
    as Subtract_Same_set.
Proof.
  unfold Subtract; intros.
  subst.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism A : (Included A)
  with signature (Same_set A ==> Same_set A ==> Basics.impl)
    as Included_Same_set.
Proof.
  unfold Basics.impl, Included; intros.
  rewrite <- H0.
  rewrite <- H in H2.
  exact (H1 _ H2).
Qed.

#[global]
Instance Included_Same_set_subrelation A :
  subrelation (@Same_set A) (@Included A).
Proof. intros ? ? [? ?]; assumption. Qed.

Add Parametric Morphism A : (Complement A)
  with signature (Same_set A ==> Same_set A)
    as Complement_Same_set.
Proof.
  split; repeat intro.
  - rewrite <- H in H1.
    now apply H0.
  - rewrite H in H1.
    now apply H0.
Qed.
