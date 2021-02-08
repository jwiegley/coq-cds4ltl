Set Warnings "-local-declaration".

Require Import
  Coq.Classes.Morphisms
  Coq.Program.Program
  Coq.Sets.Classical_sets
  Coq.Sets.Ensembles
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Same_set
  Stream
  LTL.

Module StreamLTL <: LinearTemporalLogic.

Variable a : Type.

Definition t := Ensemble (Stream a).

Definition not   := Complement (Stream a).
Definition or    := Union (Stream a).
Definition true  := Full_set (Stream a).
Definition false := Empty_set (Stream a).
Definition and   := Intersection (Stream a).
Definition impl  := Included (Stream a).

Program Instance impl_reflexive : Reflexive impl.
Next Obligation.
  unfold impl.
  now repeat intro.
Qed.
Program Instance impl_transitive : Transitive impl.
Next Obligation.
  unfold impl, Included in *.
  repeat intro.
  now intuition.
Qed.

Definition next : t -> t := λ p s,（s, 1）⊨ p.

Declare Scope ltl_scope.
Bind Scope ltl_scope with t.
Open Scope ltl_scope.

Notation "◯ p"     := (next p)    (at level 75, right associativity) : ltl_scope.

Theorem next_semantics : ∀ σ j p,（σ, j）⊨ (◯ p) <->（σ, j + 1）⊨ p.
Proof.
  unfold next.
  split; intros.
  - rewrite PeanoNat.Nat.add_comm.
    now rewrite <- from_plus.
  - rewrite PeanoNat.Nat.add_comm in H.
    now rewrite <- from_plus in H.
Qed.

Definition until : t -> t -> t :=
  λ p q s, ∃ k,（s, k）⊨ q /\ ∀ i, i < k ->（s, i）⊨ p.

Notation "p 'U' q" := (until p q) (at level 79, right associativity) : ltl_scope.

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

Definition always     : t -> t := λ p s, ∀ i,（s, i）⊨ p.
Definition eventually : t -> t := λ p s, ∃ i,（s, i）⊨ p.

Definition wait : t -> t -> t :=
  λ p q s, ∃ k,（s, k）⊨ q /\ ∀ i, i < k ->（s, i）⊨ p.

End StreamLTL.
