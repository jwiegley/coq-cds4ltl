Require Import
  Program
  Coq.Lists.List
  Coq.Relations.Relation_Definitions
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Logic.Classical
  Coq.Sets.Ensembles
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

Lemma step_correct (l : LTL a) (T : Stream a) :
  0 < length T ->
  matches a False l T
    <-> fst (fold_left (fun '(mf, acc) x =>
                          match mf with
                          | Some f => (Some f, acc)
                          | None   => step x acc
                          end) T (None, l)) = None.
Proof.
  induction T; simpl; split; intros; auto.
  - discriminate.
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
