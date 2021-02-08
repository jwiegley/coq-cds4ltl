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
Definition eqv   := Same_set (Stream a).

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

Instance eqv_equivalence : Equivalence eqv.
Proof.
  split.
  - intro x; now split.
  - repeat intro; split; destruct H; now intuition.
  - repeat intro; split; destruct H, H0; now transitivity y.
Defined.

Definition next : t -> t :=
  λ p s, (s, 1) ⊨ p.
Definition until : t -> t -> t :=
  λ p q s, ∃ i, (s, i) ⊨ q /\ ∀ k, k < i -> (s, k) ⊨ p.

End StreamLTL.
