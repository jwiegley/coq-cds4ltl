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

Section Eff.
  CoInductive Eff (T : Type) : Type :=
    | Stop  : T -> Eff T
    | Delay : Eff T -> Eff T
    | Query : (a -> Eff T) -> Eff T.

  Context {A B} (f : A -> B).

  CoFixpoint fmap' (m : Eff A) : Eff B :=
    match m with
    | Stop _ x  => Stop _ (f x)
    | Delay _ m => Delay _ (fmap' m)
    | Query _ k => Query _ (fmap' ∘ k)
    end.
End Eff.

Arguments Stop {T} _.
Arguments Delay {T} _.
Arguments Query {T} _.

Definition fmap {A B} := @fmap' A B.

CoInductive Result : Type :=
  | Failure (e : Failed)
  | Success.

Definition frob `(f : Eff A) : Eff A :=
  match f with
  | Query k => Query k
  | Delay m    => Delay m
  | Stop x     => Stop x
  end.

Theorem frob_eq : forall A (f : Eff A), f = frob f.
Proof. destruct f; reflexivity. Qed.

Open Scope ltl_scope.

Arguments expand {_} _.

Definition Machine := Eff Result.

CoFixpoint feedInput (input : a) (p : Machine) : Machine :=
  match p with
  | Query k => k input
  | Delay m    => m
  | Stop x     => Stop x
  end.

(* Implements "and" behavior *)
CoFixpoint combine (f g : Machine) : Machine :=
  match f, g with
  | Stop (Failure e), _ => Stop (Failure (LeftFailed e))
  | _, Stop (Failure e) => Stop (Failure (RightFailed e))
  | Delay f', Delay g'  => Delay (combine f' g')
  | Query f', Query g'  => Query (fun a => combine (f' a) (g' a))
  | f', Query g'        => Query (fun a => combine f' (g' a))
  | Query f', g'        => Query (fun a => combine (f' a) g')
  | f', Stop Success    => f'
  | Stop Success, g'    => g'
  end.

(* Implements "or" behavior *)
CoFixpoint select (f g : Machine) : Machine :=
  match f, g with
  | Stop (Failure e1),
    Stop (Failure e2)    => Stop (Failure (BothFailed e1 e2))
  | Stop Success, _      => Stop Success
  | _, Stop Success      => Stop Success
  | Delay f', Delay g'   => Delay (select f' g')
  | Query f', Query g'   => Query (fun a => select (f' a) (g' a))
  | f', Query g'         => Query (fun a => select f' (g' a))
  | Query f', g'         => Query (fun a => select (f' a) g')
  | Stop (Failure _), g' => g'
  | f', Stop (Failure _) => f'
  end.

Definition not_complex (l : LTL a) : Prop :=
  match l with
  | p U q => False
  | p R q => False
  | _     => True
  end.

Lemma not_complex_expand : forall l, not_complex (expand l).
Proof. induction l; simpl; auto. Qed.

Ltac follows :=
  match goal with
    [ H : LTL a |- _ ] =>
    induction H; simpl in *; eexists; eauto; try reflexivity
  end.

Definition step (m : Machine) (x : a) : Machine :=
  match m with
  | Stop x  => Stop x
  | Delay m => m
  | Query f => f x
  end.

Fixpoint run (m : Machine) (l : list a) : Machine :=
  match l with
  | [] => m
  | x :: xs => run (step m x) xs
  end.

Definition until' pq (p q : Machine) : Machine := select q (combine p pq).

(* CoFixpoint until (p q : Machine) : Machine := until' (until p q) p q. *)

Fixpoint compile (l : LTL a) : Machine :=
  match l with
  | ⊤ => Stop Success
  | ⊥ => Stop (Failure HitBottom)

  | Accept v => Query (compile ∘ v)
  | Reject v =>
    Query (fun x =>
                let cofix go m :=
                    match m with
                    | Stop (Failure _) => Stop Success
                    | Stop Success     => Stop (Failure (Rejected x))
                    | Delay m          => Delay (go m)
                    | Query k       => Query (go ∘ k)
                    end in go (compile (v x)))

  | p ∧ q => combine (compile p) (compile q)
  | p ∨ q => select (compile p) (compile q)

  | X p   => Delay (compile p)

  | p U q => select (compile q) (combine (compile p) (Delay (compile (p U q))))
  | p R q => combine (compile q) (select (compile p) (Delay (compile (p R q))))
  end.

Lemma run_correct (l : LTL a) (s : Stream a) :
  (* Because matches may be partial on finite input, we only ensure that a
     non-failing match is never a failure, and vice versa. *)
  matches a l s
    <-> forall e, run (compile l) s <> Stop (Failure e).
Proof.
Abort.

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
