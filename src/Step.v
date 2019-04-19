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
    | Stop     : T -> Eff T
    | Delay    : Eff T -> Eff T
    | DelayAsk : Query T -> Eff T

  with Query (T : Type) : Type :=
    | Ask : (a -> Eff T) -> Query T.

  Context {A B} (f : A -> B).

  CoFixpoint fmap' (m : Eff A) : Eff B :=
    match m with
    | Stop _ x     => Stop _ (f x)
    | Delay _ m    => Delay _ (fmap' m)
    | DelayAsk _ m => DelayAsk _ (fmapQuery m)
    end

  with fmapQuery (m : Query A) : Query B :=
    match m with
    | Ask _ k => Ask _ (fmap' ∘ k)
    end.
End Eff.

Arguments Stop {T} _.
Arguments Delay {T} _.
Arguments DelayAsk {T} _.
Arguments Ask {T} _.

Definition fmap {A B} := @fmap' A B.

CoInductive Result : Type :=
  | Failure (e : Failed)
  | Success.

Definition frob `(f : Eff A) : Eff A :=
  match f with
  | Stop x     => Stop x
  | Delay  m   => Delay m
  | DelayAsk x => DelayAsk x
  end.

Definition frobQuery `(f : Query A) : Query A :=
  match f with
  | Ask k    => Ask k
  end.

Theorem frob_eq : forall A (f : Eff A), f = frob f.
Proof. destruct f; reflexivity. Qed.

Theorem frobQuery_eq : forall A (f : Query A), f = frobQuery f.
Proof. destruct f; reflexivity. Qed.

Open Scope ltl_scope.

Arguments expand {_} _.

Inductive Machine :=
  | Ready (e : Eff Result)
  | Waiting (q : Query Result).

(* Implements "and" behavior *)
CoFixpoint combineEff (f g : Eff Result) : Eff Result :=
  match f, g with
  | Stop (Failure e), _ => Stop (Failure (LeftFailed e))
  | _, Stop (Failure e) => Stop (Failure (RightFailed e))
  | Delay f', Delay g'  => Delay (combineEff f' g')

  | DelayAsk f', DelayAsk g' => DelayAsk (combineQuery f' g')

  | Delay f', DelayAsk (Ask g')    =>
    DelayAsk (Ask (fun a => combineEff f' (g' a)))

  | DelayAsk (Ask f'), Delay g'    =>
    DelayAsk (Ask (fun a => combineEff (f' a) g'))

  | f', Stop Success         => f'
  | Stop Success, g'         => g'
  end

with combineQuery (f g : Query Result) : Query Result :=
  match f, g with
  | Ask f', Ask g' => Ask (fun a => combineEff (f' a) (g' a))
  end.

Definition combine (f g : Machine) : Machine :=
  match f, g with
  | Ready f', Ready g'         => Ready (combineEff f' g')
  | Ready f', Waiting (Ask g') => Waiting (Ask (fun a => combineEff f' (g' a)))
  | Waiting (Ask f'), Ready g' => Waiting (Ask (fun a => combineEff (f' a) g'))
  | Waiting f', Waiting g'     => Waiting (combineQuery f' g')
  end.

(* Implements "or" behavior *)
CoFixpoint selectEff (f g : Eff Result) : Eff Result :=
  match f, g with
  | Stop (Failure e1),
    Stop (Failure e2)    => Stop (Failure (BothFailed e1 e2))
  | Stop Success, _      => Stop Success
  | _, Stop Success      => Stop Success
  | Delay f', Delay g'   => Delay (selectEff f' g')

  | DelayAsk f', DelayAsk g' => DelayAsk (selectQuery f' g')

  | Delay f', DelayAsk (Ask g') =>
    DelayAsk (Ask (fun a => selectEff f' (g' a)))

  | DelayAsk (Ask f'), Delay g' =>
    DelayAsk (Ask (fun a => selectEff (f' a) g'))

  | Stop (Failure _), g' => g'
  | f', Stop (Failure _) => f'
  end

with selectQuery (f g : Query Result) : Query Result :=
  match f, g with
  | Ask f', Ask g' => Ask (fun a => selectEff (f' a) (g' a))
  end.

Definition select (f g : Machine) : Machine :=
  match f, g with
  | Ready f', Ready g'         => Ready (selectEff f' g')
  | Ready f', Waiting (Ask g') => Waiting (Ask (fun a => selectEff f' (g' a)))
  | Waiting (Ask f'), Ready g' => Waiting (Ask (fun a => selectEff (f' a) g'))
  | Waiting f', Waiting g'     => Waiting (selectQuery f' g')
  end.

Definition answer (m : Query Result) (x : a) : Eff Result :=
  match m with
  | Ask k => k x
  end.

(* Resolve any queries the machine may have, reducing it to an [Eff]. *)
Definition resolve (m : Machine) (x : a) : Eff Result :=
  match m with
  | Ready (Stop x)     => Stop x
  | Ready (Delay m)    => Delay m
  | Ready (DelayAsk m) => DelayAsk m
  | Waiting (Ask k)    => k x
  end.

Definition defer (m : Machine) : Eff Result :=
  match m with
  | Ready m   => Delay m
  | Waiting q => DelayAsk q
  end.

Definition step (m : Machine) (x : a) : Machine :=
  match m with
  | Ready (Stop x)     => Ready (Stop x)
  | Ready (Delay m)    => Ready m
  | Ready (DelayAsk m) => Waiting m
  | Waiting (Ask k)    => Ready (k x)
  end.

Definition run (m : Machine) (xs : list a) : Machine :=
  fold_left step xs m.

Fixpoint compile (l : LTL a) : Machine :=
  match l with
  | ⊤ => Ready (Stop Success)
  | ⊥ => Ready (Stop (Failure HitBottom))

  | Accept v => Waiting (Ask (fun a => resolve (compile (v a)) a))
  | Reject v =>
    Waiting (Ask (fun x =>
                    fmap (fun m =>
                            match m with
                            | Failure _ => Success
                            | Success     => Failure (Rejected x)
                            end)
                         (resolve (compile (v x)) x)))

  | p ∧ q => combine (compile p) (compile q)
  | p ∨ q => select (compile p) (compile q)

  | X p   => Ready (defer (compile p))

  | p U q => select (compile q) (combine (compile p) (Ready (defer (compile (p U q)))))
  | p R q => combine (compile q) (select (compile p) (Ready (defer (compile (p R q)))))
  end.

Lemma run_correct (l : LTL a) (s : Stream a) :
  (* Because matches may be partial on finite input, we only ensure that a
     non-failing match is never a failure, and vice versa. *)
  matches a l s
    <-> forall e, run (compile l) s <> Ready (Stop (Failure e)).
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
