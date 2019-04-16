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

Open Scope ltl_scope.

Fixpoint fuel_needed (l : LTL a) : option nat :=
  match l with
  | ⊤        => Some 0
  | ⊥        => Some 0
  | Accept v => Some 1
  | Reject v => Some 1
  | ¬ p      => fuel_needed p
  | p ∧ q    => liftA2 max (fuel_needed p) (fuel_needed q)
  | p ∨ q    => liftA2 min (fuel_needed p) (fuel_needed q)
  | X p      => liftA2 plus (Some 1) (fuel_needed p)
  | p U q    => fuel_needed q
  | p R q    => fuel_needed q
  | ◇ p      => fuel_needed p
  | □ p      => None
  end.

Ltac fromJust :=
  match goal with
    [ H : Just _ = Just _ |- _ ] =>
    inversion H; subst; clear H
  end.

Lemma fuel_needed_by_expand l : forall n m,
  fuel_needed (expand a l) = Some n ->
  fuel_needed l = Some m ->
  n <= m.
Proof.
  induction l; simpl in *; intros;
  unfold Maybe_map, Maybe_apply in *;
  repeat fromJust;
  try destruct (fuel_needed (expand a l1)) eqn:?;
  try destruct (fuel_needed (expand a l2)) eqn:?;
  try destruct (fuel_needed l1) eqn:?;
  try destruct (fuel_needed l2) eqn:?;
  repeat fromJust;
  try discriminate; auto;
  try apply Nat.max_le_compat; auto;
  try apply Nat.min_le_compat; auto.
  - destruct (fuel_needed (expand a l)) eqn:?;
    destruct (fuel_needed l) eqn:?;
    try discriminate;
    repeat fromJust.
    apply le_n_S.
    now apply IHl.
  - now apply Nat.min_le_iff; auto.
  - now apply Nat.min_le_iff; auto.
  - apply Nat.max_lub_iff; auto.
    intuition auto.
    admit.
  - admit.
  - destruct (fuel_needed (expand a l)) eqn:?;
    destruct (fuel_needed l) eqn:?;
    try discriminate;
    repeat fromJust.
    now apply Nat.min_le_iff; auto.
Admitted.

Inductive Failed : Type :=
  | HitBottom
  | Rejected    (x : a)
  | BothFailed  (p q : Failed)
  | LeftFailed  (p : Failed)
  | RightFailed (q : Failed)
  | Unexpected  (l : LTL a).

Open Scope ltl_scope.

Fixpoint step (i : a) (l : LTL a) : option Failed * LTL a :=
  match l with
  | ⊤ => (None, l)
  | ⊥ => (Some HitBottom, l)

  | ¬ p => (Some (Unexpected p), p)

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
    | (Some f1, l1), (None, l2)    => (None, l1 ∨ l2)
    | (None, l1),    (_, l2)       => (None, l1 ∨ l2)
    end

  | X p => (None, p)

  | p U q =>
    (* φ U ψ ≈ ψ ∨ (φ ∧ X(φ U ψ)) *)
    match step i q, step i p with
    | (Some f1, l1), (Some f2, l2) => (Some (BothFailed f1 f2), l2 U l1)
    | (Some f1, l1), (None, l2)    => (None, l2 U l1)
    | (None, l1),    (_, l2)       => (None, l2 U l1)
    end

  | p R q =>
    (* φ R ψ ≈ ψ ∧ (φ ∨ X(φ R ψ)) *)
    match step i q, step i p with
    | (Some f1, l1), (_, l2)       => (Some (RightFailed f1), l2 R l1)
    | (None, l1),    (Some f2, l2) => (Some (LeftFailed f2), l2 R l1)
    | (None, l1),    (None, l2)    => (None, l2 R l1)
    end

  | ◇ p =>
    (* ◇ φ ≈ φ ∨ X(◇ φ) *)
    match step i p with
    | (Some f, _) => (None, ◇ p)
    | (None,   l) => (None, ⊤)
    end

  | □ p =>
    (* □ φ ≈ φ ∧ X(□ φ) *)
    match step i p with
    | (Some f, _) => (Some f, ⊥)
    | (None,   l) => (None, □ p)
    end
  end.

Fixpoint stream_fold {A B : Type}
         (f : A -> B -> A) (s : Stream B) (z : A) : A :=
  match s with
  | Cons _ x xs => stream_fold f xs (f z x)
  end.

Lemma step_correct (l : LTL a) (x : a) (xs : Stream a) :
  IF matches a l (Cons _ x xs)
  then fst (step x l) = None
  else exists f, fst (step x l) = Some f.
Proof.
  induction l.
  - simpl; left; intuition.
  - simpl; right; eauto.
  - simpl; intuition; discriminate.
  - simpl.
    destruct (H x), H0.
      right; intuition.
      destruct (step x (v x)) eqn:?.
      destruct o; simpl in *.
        discriminate.
      eauto.
    left; intuition.
    destruct H1.
    destruct (step x (v x)) eqn:?.
    destruct o; simpl in *; auto.
    discriminate.
  - admit.
  - destruct IHl1, IHl2.
    + left; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto.
    + right; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto.
      simpl; eexists; eauto.
    + right; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto.
      simpl; eexists; eauto.
    + right; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto;
      simpl; eexists; eauto.
  - destruct IHl1, IHl2.
    + left; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto.
    + left; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto.
    + left; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto.
    + right; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto;
      simpl; eexists; eauto.
  - destruct IHl.
    + left; simpl; intuition.
      admit.
    + right; simpl; intuition.
        admit.
      admit.
  - destruct IHl2.
      left; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto.
    destruct IHl1.
      left; simpl; intuition auto.
      right; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto.
      simpl; eexists; eauto.
    + right; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto.
      simpl; eexists; eauto.
    + right; simpl; intuition.
      destruct (step x l1) eqn:?, o;
      destruct (step x l2) eqn:?, o;
      try discriminate; auto;
      simpl; eexists; eauto.
  - admit.
  - admit.
  - admit.
  try discriminate; intuition auto.
  intuition.
    destruct T; simpl in *; intuition.
    simpl.
  - inversion H.
    specialize (IHT H2).
    clear H.
    clear -H2.
    clear H H2.
    intuition auto.
    intuition.
    apply IHT.
    inversion H; clear H; intuition.
  - inversion H; clear H; intuition.
Qed.

End Step.

Section Examples.

Open Scope list_scope.
Open Scope ltl_scope.

Definition sample :=
  let formula :=
      □ (ifThen (fun n => n =? 3) (fun n => ◇ (num (n + 5)))) in
  let f0 := pnf _ formula in
  let (r1, f1) := step nat 1 (expand _ f0) in
  let (r2, f2) := step nat 2 (expand _ f1) in
  let (r3, f3) := step nat 3 (expand _ f2) in
  let (r4, f4) := step nat 4 (expand _ f3) in
  let (r5, f5) := step nat 5 (expand _ f4) in
  let (r6, f6) := step nat 6 (expand _ f5) in
  let (r7, f7) := step nat 7 (expand _ f6) in
  let (r8, f8) := step nat 8 (expand _ f7) in
  let (r9, _)  := step nat 9 (expand _ f8) in
  ([r1; r2; r3; r4; r5; r6; r7; r8; r9],
   [expand _ f0;
    expand _ f1;
    expand _ f2;
    expand _ f3;
    expand _ f4;
    expand _ f5;
    expand _ f6;
    expand _ f7;
    expand _ f8]).

Goal True.
  pose (fst sample).
  pose (map (prune _) (snd sample)).
  unfold sample in l, l0.
  simpl in l, l0.
Abort.

End Examples.
