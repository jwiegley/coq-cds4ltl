Require Import
  Program
  Coq.Lists.List
  Coq.Relations.Relation_Definitions
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Logic.Classical
  Coq.Sets.Ensembles
  Hask.Control.Monad
  Hask.Prelude.

Open Scope program_scope.
Open Scope list_scope.

Require Import LTL.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Section Step.

Variable a : Type.              (* The type of entries in the trace *)

Inductive Failed : Type :=
  | HitBottom
  | Rejected    (x : a)
  | BothFailed  (p q : Failed)
  | LeftFailed  (p : Failed)
  | RightFailed (q : Failed).

Open Scope ltl_scope.

Fixpoint step (i : a) (l : LTL a) : option Failed * LTL a :=
  match l with
  | ⊤ => (None, l)
  | ⊥ => (Some HitBottom, l)

  | Accept v => step i (v i)
  | Reject v =>
    match step i (v i) with
    | (None, l)   => (Some (Rejected i), l)
    | (Some _, l) => (None, l)
    end

  | p ∧ q =>
    match step i p, step i q with
    | (Some f1, l1), (_, l2)       => (Some (LeftFailed f1), l1 ∧ l2)
    | (None, l1),    (Some f2, l2) => (Some (RightFailed f2), l1 ∧ l2)
    | (None, l1),    (None, l2)    => (None, l1 ∧ l2)
    end

  | p ∨ q =>
    match step i p, step i q with
    | (Some f1, l1), (Some f2, l2) => (Some (BothFailed f1 f2), l1 ∨ l2)
    | (Some f1, l1), (None, l2)    => (None, l2)
    | (None, l1),    (Some f2, l2) => (None, l1)
    | (None, l1),    (None, l2)    => (None, l1 ∨ l2)
    end

  | X p => (None, p)

  | p U q =>
    (* φ U ψ ≈ ψ ∨ (φ ∧ X(φ U ψ)) *)
    match step i q, step i p with
    | (Some f1, l1), (Some f2, l2) => (Some (BothFailed f1 f2), l2 U l1)
    | (Some f1, l1), (None, l2)    => (None, l2 U q)
    | (None, l1),    (Some f2, l2) => (None, p  U l1)
    | (None, l1),    (None, l2)    => (None, l2 U l1)
    end

  | p R q =>
    (* φ R ψ ≈ ψ ∧ (φ ∨ X(φ R ψ)) *)
    match step i q, step i p with
    | (None, l1),    (Some f2, l2) => (None, p  R l1)
    | (None, l1),    (None, l2)    => (None, l2 R l1)
    | (Some f1, l1), (None, l2)    => (Some (RightFailed f1), l2 R l1)
    | (Some f1, l1), (Some f2, l2) => (None, p  R q)
    end
  end.

Lemma step_correct (l : LTL a) (x : a) (xs : Stream a) :
  matches a l (x :: xs) <-> fst (step x l) = None.
Proof.
Admitted.

End Step.

Section Examples.

Open Scope list_scope.
Open Scope ltl_scope.

Definition sample :=
  let formula :=
      □ (ifThen (fun n => n =? 3) (fun n => ◇ (num (n + 5)))) in
  let f0 := formula in
  let (r1, f1) := step nat 1 f0 in
  let (r2, f2) := step nat 2 f1 in
  let (r3, f3) := step nat 3 f2 in
  let (r4, f4) := step nat 4 f3 in
  let (r5, f5) := step nat 5 f4 in
  let (r6, f6) := step nat 6 f5 in
  let (r7, f7) := step nat 7 f6 in
  let (r8, f8) := step nat 8 f7 in
  let (r9, _)  := step nat 9 f8 in
  ([r1; r2; r3; r4; r5; r6; r7; r8; r9],
   [f0; f1; f2; f3; f4; f5; f6; f7; f8]).

Goal True.
  pose (fst sample).
  pose (map (prune _) (snd sample)).
  unfold sample in l, l0.
  simpl in l, l0.
Abort.

End Examples.
