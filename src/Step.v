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
    | Pure : T -> Eff T
    | Delay : Eff T -> Eff T
    | Interact : (a -> Eff T) -> Eff T.

  Context {A B} (k : A -> Eff B).

  CoFixpoint bind' (c : Eff A) : Eff B :=
    match c with
    | Pure _ v => k v
    | Delay _ d => Delay _ (bind' d)
    | Interact _ k' => Interact _ (fun x => bind' (k' x))
    end.

  Context (f : A -> B).

  CoFixpoint fmap' (m : Eff A) : Eff B :=
    match m with
    | Pure _ x     => Pure _ (f x)
    | Delay _ m    => Delay _ (fmap' m)
    | Interact _ k => Interact _ (fmap' ∘ k)
    end.
End Eff.

Arguments Pure {T} _.
Arguments Delay {T} _.
Arguments Interact {T} _.

Definition bind {A B} c k := @bind' A B k c.
Definition fmap {A B} := @fmap' A B.

CoInductive Result : Type :=
  | Failure (e : Failed)
  | Success.

Definition frob `(f : Eff A) : Eff A :=
  match f with
  | Interact k => Interact k
  | Delay m    => Delay m
  | Pure x     => Pure x
  end.

Theorem frob_eq : forall A (f : Eff A), f = frob f.
Proof. destruct f; reflexivity. Qed.

Open Scope ltl_scope.

Arguments expand {_} _.

Definition Machine := Eff Result.

CoFixpoint feedInput (input : a) (p : Machine) : Machine :=
  match p with
  | Interact k => k input
  | Delay m    => m
  | Pure x     => Pure x
  end.

(* Implements "and" behavior *)
CoFixpoint combine (f g : Machine) : Machine :=
  match f, g with
  | Pure (Failure e), _      => Pure (Failure (LeftFailed e))
  | _, Pure (Failure e)      => Pure (Failure (RightFailed e))
  | f', Pure Success         => f'
  | Pure Success, g'         => g'
  | Delay f', Delay g'       => Delay (combine f' g')
  | Delay f', Interact g'    => Interact (fun a => combine (Delay f') (g' a))
  | Interact f', Delay g'    => Interact (fun a => combine (f' a) (Delay g'))
  | Interact f', Interact g' => Interact (fun a => combine (f' a) (g' a))
  end.

(* Implements "or" behavior *)
CoFixpoint select (f g : Machine) : Machine :=
  match f, g with
  | Pure (Failure e1),
    Pure (Failure e2)        => Pure (Failure (BothFailed e1 e2))
  | Pure Success, _          => Pure Success
  | _, Pure Success          => Pure Success
  | Pure (Failure _), g'     => g'
  | f', Pure (Failure _)     => f'
  | Delay f', Delay g'       => Delay (combine f' g')
  | Delay f', Interact g'    => Interact (fun a => combine (Delay f') (g' a))
  | Interact f', Delay g'    => Interact (fun a => combine (f' a) (Delay g'))
  | Interact f', Interact g' => Interact (fun a => select (f' a) (g' a))
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

CoFixpoint compile' (l : LTL a) : Machine :=
  match l with
  | ⊤ => Pure Success
  | ⊥ => Pure (Failure HitBottom)

  | Accept v => Interact (fun x => compile' (v x))
  | Reject v =>
    Interact (fun x =>
                fmap (fun m =>
                        match m with
                        | Failure e => Success
                        | Success   => Failure (Rejected x)
                        end) (compile' (v x)))

  | p ∧ q => combine (compile' p) (compile' q)
  | p ∨ q => select (compile' p) (compile' q)
  | X p   => Delay (compile' (expand p))
  | p U q => Pure Success       (* is never called due to expand *)
  | p R q => Pure Success       (* is never called due to expand *)
  end.

CoFixpoint compile (l : LTL a) : Machine := compile (expand l).

Fixpoint runMachine (m : Machine) (x : a) : Machine :=
  match m with
  | Pure x     => x
  | Delay m    => m
  | Interact f => f x
  end.

Lemma step_correct (l : LTL a) (s : Stream a) :
  matches a l s
    <-> forall e, runMachine (compile l) s <> Pure (Failure e).
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
