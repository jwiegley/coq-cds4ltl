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
  | EndOfTrace
  | Rejected    (x : a)
  | BothFailed  (p q : Failed)
  | LeftFailed  (p : Failed)
  | RightFailed (q : Failed).

Inductive Result : Type :=
  (* | Ask (f : a -> Result) *)
  | Failure (e : Failed)
  | Continue (l : LTL a)
  | Success.

(*
Definition frob `(f : Eff A) : Eff A :=
  match f with
  | Stop x  => Stop x
  | Delay m => Delay m
  | Repeat  => Repeat
  | Ask k   => Ask k
  end.

Theorem frob_eq : forall A (f : Eff A), f = frob f.
Proof. destruct f; reflexivity. Qed.
*)

Open Scope ltl_scope.

Arguments expand {_} _.

Definition and (f g : Result) : Result :=
  match f, g with
  | Failure e, _   => Failure (LeftFailed e)
  | _, Failure e   => Failure (RightFailed e)
  | Continue f',
    Continue g'    => Continue (f' ∧ g')
  | f', Success    => f'
  | Success, g'    => g'
  (* | Ask f', Ask g' => Ask (fun a => and (f' a) (g' a)) *)
  (* | f', Ask g'     => Ask (fun a => and f' (g' a)) *)
  (* | Ask f', g'     => Ask (fun a => and (f' a) g') *)
  end.

Definition or (f g : Result) : Result :=
  match f, g with
  | Failure e1,
    Failure e2     => Failure (BothFailed e1 e2)
  | Success, _     => Success
  | _, Success     => Success
  | Continue f',
    Continue g'    => Continue (f' ∨ g')
  | Failure _, g'  => g'
  | f', Failure _  => f'
  (* | Ask f', Ask g' => Ask (fun a => and (f' a) (g' a)) *)
  (* | f', Ask g'     => Ask (fun a => and f' (g' a)) *)
  (* | Ask f', g'     => Ask (fun a => and (f' a) g') *)
  end.

Definition Machine := option a -> Result.

Fixpoint compile (l : LTL a) : Machine := fun mx =>
  match l with
  | ⊤ => Success
  | ⊥ => Failure HitBottom

  | Accept v =>
    match mx with
    | None   => Failure EndOfTrace
    | Some x => compile (v x) (Some x)
    end
  | Reject v =>
    match mx with
    | None   => Success
    | Some x =>
      match compile (v x) (Some x) with
      | Failure _  => Success
      | Success    => Failure (Rejected x)
      | Continue p => Continue (negate _ p)
      end
    end

  | p ∧ q => and (compile p mx) (compile q mx)
  | p ∨ q => or  (compile p mx) (compile q mx)

  | X p   =>
    match mx with
    | None   => Failure EndOfTrace
    | Some _ => Continue p
    end

  | p U q =>
    match mx with
    | None   => compile q None
    | Some x => or (compile q mx) (and (compile p mx) (Continue (p U q)))
    end

  | p R q =>
    match mx with
    | None   => and (compile q None) (compile p None)
    | Some x => and (compile q mx) (or (compile p mx) (Continue (p R q)))
    end
  end.

Definition step (m : Result) (x : a) : Result :=
  match m with
  | Continue l => compile l (Some x)
  | r => r
  end.

Definition and_then (r : Result) (s : LTL a -> Result) : Result :=
  match r with
  | Continue l => s l
  | r => r
  end.

Fixpoint run (m : LTL a) (xs : list a) : Result :=
  match xs with
  | []      => compile m None
  | x :: xs => and_then (compile m (Some x)) (fun l => run l xs)
  end.

Definition passes (r : Result) : Prop :=
  match r with
  | Failure e  => False
  | Continue _ => True
  | Success    => True
  end.

Definition passes_equiv (p q : Result) : Prop :=
  passes p <-> passes q.
Arguments passes_equiv p q /.

Global Program Instance Equivalence_passes_equiv : Equivalence passes_equiv.
Next Obligation.
  unfold passes_equiv.
  repeat intro; auto.
  reflexivity.
Qed.
Next Obligation.
  unfold passes_equiv.
  repeat intro; intuition.
Qed.
Next Obligation.
  unfold passes_equiv.
  repeat intro; firstorder.
Qed.

Lemma run_and p q xs :
  passes (run (p ∧ q) xs) <-> passes (run p xs) /\ passes (run q xs).
Proof.
  generalize dependent p.
  generalize dependent q.
  induction xs; simpl; intros;
  intuition auto;
  try destruct (compile p Nothing) eqn:?;
  try destruct (compile q Nothing) eqn:?;
  try destruct (compile p (Some a0)) eqn:?;
  try destruct (compile q (Some a0)) eqn:?;
  try specialize (proj1 (IHxs _ _) H); intros;
  simpl in *; now intuition.
Qed.

Lemma run_reject p xs :
  passes (run (¬ p) xs) <->
  passes (match run p xs with
          | Failure _  => Success
          | Success    => Failure HitBottom
          | Continue p => Continue (negate _ p)
          end).
Proof.
  generalize dependent p.
  induction xs; simpl; intros;
  unfold and_then, Basics.compose;
  intuition auto;
  try destruct (compile (p a0) Nothing) eqn:?;
  try destruct (compile (p a0) (Just a0)) eqn:?;
  try specialize (proj1 (IHxs _ _) H); intros;
  intuition.
  - induction p; intuition.
  - admit.
  - admit.
  -
Abort.

Lemma run_or p q xs :
  passes (run (p ∨ q) xs) <-> passes (run p xs) \/ passes (run q xs).
Proof.
  generalize dependent p.
  generalize dependent q.
  induction xs; simpl; intros;
  intuition auto;
  try destruct (compile p Nothing) eqn:?;
  try destruct (compile q Nothing) eqn:?;
  try destruct (compile p (Some a0)) eqn:?;
  try destruct (compile q (Some a0)) eqn:?;
  try specialize (proj1 (IHxs _ _) H); intros;
  simpl in *; now intuition.
Qed.

Lemma run_next p x xs :
  passes (run (X p) (x :: xs)) <-> passes (run p xs).
Proof. now induction xs; intuition. Qed.

Lemma run_until p q s :
  passes (run (p U q) s) <->
  let fix go s :=
      match s with
      | [] => passes (run q s)
      | _ :: xs => passes (run q s) \/ (passes (run p s) /\ go xs)
      end in go s.
Proof.
  generalize dependent p.
  generalize dependent q.
  induction s; simpl; intros.
  - split; auto.
  - destruct (compile p (Some a0)) eqn:?;
    destruct (compile q (Some a0)) eqn:?; simpl;
    intuition auto.
    + apply run_and in H.
      intuition.
    + apply IHs in H1.
      apply run_and; auto.
    + apply run_or in H.
      destruct H; auto.
      apply run_and in H.
      intuition.
    + apply run_or.
      intuition.
    + apply IHs in H1.
      apply run_or; intuition.
      right.
      apply run_and; auto.
    + right.
      split; auto.
      now apply IHs.
    + now apply IHs in H1.
    + apply run_or in H.
      intuition.
    + apply run_or.
      intuition.
    + apply IHs in H1.
      apply run_or.
      intuition.
Qed.

Lemma run_release p q s :
  passes (run (p R q) s) <->
  let fix go s :=
      match s with
      | [] => passes (run q s) /\ passes (run p s)
      | _ :: xs => passes (run q s) /\ (passes (run p s) \/ go xs)
      end in go s.
Proof.
  generalize dependent p.
  generalize dependent q.
  induction s; intros.
  - split; intros.
      now apply run_and.
    pose (run_and q p []).
    simpl in *; intuition.
  - simpl; unfold and_then; split; intros;
    destruct (compile p (Some a0)) eqn:?;
    destruct (compile q (Some a0)) eqn:?; simpl in *;
    intuition auto.
    + apply run_and in H.
      now intuition.
    + apply run_and in H.
      now intuition.
    + apply IHs in H.
      now right.
    + apply run_and in H.
      now intuition.
    + apply run_and in H.
      destruct H.
      apply run_or in H0.
      now intuition.
    + apply run_or in H.
      now intuition.
    + apply run_and.
      now intuition.
    + now apply IHs.
    + apply run_and.
      split; auto.
      apply run_or.
      now intuition.
    + apply run_and.
      split; auto.
      apply run_or.
      now intuition.
    + apply run_or.
      now intuition.
    + apply run_or.
      now intuition.
Qed.

Lemma run_correct (l : LTL a) (s : Stream a) :
  matches a l s <-> passes (run l s).
Proof.
  generalize dependent s.
  induction l; simpl; intros.
  - now induction s.
  - now induction s.
  - induction s; intuition.
    now specialize (proj1 (H _ _) H2).
  - induction s.
      now intuition.
    admit.
  - split; intros.
      destruct H.
      specialize (proj1 (IHl1 _) H); intros; clear IHl1 H.
      specialize (proj1 (IHl2 _) H0); intros; clear IHl2 H0.
      now apply run_and.
    apply run_and in H.
    now split; intuition.
  - split; intros.
      destruct H.
        specialize (proj1 (IHl1 _) H); intros; clear IHl1 H.
        apply run_or.
        now left.
      specialize (proj1 (IHl2 _) H); intros; clear IHl2 H.
      apply run_or.
      now right.
    apply run_or in H.
    now intuition.
  - now induction s; intuition.
  - split; intros.
      apply run_until.
      simpl.
      induction s; intuition.
    apply run_until in H.
    induction s; intuition.
  - split; intros.
      apply run_release.
      simpl.
      induction s; intuition.
    apply run_release in H.
    induction s; intuition.
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
