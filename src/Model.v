Require Import
  Coq.Classes.Morphisms
  Coq.Program.Program
  Coq.Sets.Classical_sets
  Coq.Sets.Ensembles
  Same_set
  Stream
  LTL.

Module StreamLTL <: LinearTemporalLogic.

Variable a : Type.

Definition t := Ensemble (Stream a).

Definition equiv := Same_set (Stream a).
Definition not := Complement (Stream a).
Definition and := Intersection (Stream a).
Definition or := Union (Stream a).

Definition next (p : t) : t := fun s => p (from 1 s).
Definition until (p q : t) : t :=
  fun s => exists i, q (from i s) /\ forall k, k < i -> p (from k s).

Fail End StreamLTL.
