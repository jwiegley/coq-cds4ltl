Set Warnings "-local-declaration".

Require Import
  Coq.Classes.Morphisms
  Coq.Program.Program
  Coq.Sets.Classical_sets
  Coq.Sets.Ensembles
  Coq.Unicode.Utf8
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

Definition next : t -> t :=
  λ p s, (s, 1) ⊨ p.

Theorem next_semantics : ∀ σ j p, (σ, j) ⊨ ◯ p <-> (σ, j + 1) ⊨ p.
Proof.
  unfold next.
  split; intros.
  - rewrite PeanoNat.Nat.add_comm.
    now rewrite <- from_plus.
  - rewrite PeanoNat.Nat.add_comm in H.
    now rewrite <- from_plus in H.
Qed.

Definition until : t -> t -> t :=
  λ p q s, ∃ i, (s, i) ⊨ q /\ ∀ k, k < i -> (s, k) ⊨ p.

Definition always     : t -> t := λ p s, ∀ i, (s, i) ⊨ p.
Definition eventually : t -> t := λ p s, ∃ i, (s, i) ⊨ p.

Definition wait : t -> t -> t :=
  λ p q s, ∃ i, (s, i) ⊨ q /\ ∀ k, k < i -> (s, k) ⊨ p.

End StreamLTL.
