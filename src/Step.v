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
    | None   => compile p None
    | Some _ => Continue p
    end

  | p U q =>
    match mx with
    | None   => compile q None
    | Some x => or (compile q mx) (and (compile p mx) (Continue (p U q)))
    end

  | p R q =>
    match mx with
    | None   => compile q None
    | Some x => and (compile q mx) (or (compile p mx) (Continue (p R q)))
    end
  end.

Definition step (m : Result) (x : a) : Result :=
  match m with
  | Continue l => compile l (Some x)
  | r => r
  end.

Function run (m : LTL a) (xs : list a) : Result :=
  match xs with
  | []      => compile m None
  | x :: xs =>
    match compile m (Some x) with
    | Continue l => run l xs
    | r => r
    end
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
      | [] => passes (run q s)
      | _ :: xs => passes (run q s) /\ (passes (run p s) \/ go xs)
      end in go s.
Proof.
  generalize dependent p.
  generalize dependent q.
  induction s; intros.
  - now intuition.
  - simpl; split; intros;
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

Lemma foo l s :
  matches a l s <-> passes (compile l (match s with
                                       | [] => None
                                       | x :: _ => Some x
                                       end)).
Proof.
  generalize dependent s.
  induction l; simpl in *; intros;
  try specialize (H x); intuition auto.
(*
  - now apply (H s).
  - now apply (H x xs).
  - destruct (compile (v x) (Just x)) eqn:?;
    simpl in *; intuition.
    pose proof (proj2 (H x xs)).
    setoid_rewrite Heqr in H1; simpl in *.
    specialize (H1 I).
    contradiction.
  - destruct (compile (v x) (Just x)) eqn:?;
    simpl in *; intuition.
      pose proof (proj1 (H x xs)).
      setoid_rewrite Heqr in H2; simpl in *.
      intuition.
    pose proof (proj2 (H x xs)).
    setoid_rewrite Heqr in H2; simpl in *.
    intuition.
*)
Admitted.

Lemma run_correct (l : LTL a) (s : Stream a) :
  matches a l s <-> passes (run l s).
Proof.
(*
  apply run_ind; simpl; split; intros; subst.
  induction l, s using run_ind.
  generalize dependent s.
  induction l; simpl; intros.
  induction
  split; intros.
    pose proof (proj1 (foo _ _) H).
    generalize dependent l.
    induction s; simpl in *; intros; auto.
    destruct (compile l (Just a0)); simpl in *; auto.
    admit.
    admit.
  destruct (compile l (Just a0)); simpl in *; auto.
  apply IHs.
  apply H.
*)
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
  - split; intros;
    induction s; intuition.
    now apply IHl in H.
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

Goal passes _ (run _ (□ (num 3 → num 4)) [2; 3]).
  simpl.
Abort.

Goal passes _ (run _ (□ (num 3 → ◇ (num 8)))
                     [1; 2; 3; 4; 5; 6; 7; 8; 9]).
  simpl.
Abort.

End Examples.
