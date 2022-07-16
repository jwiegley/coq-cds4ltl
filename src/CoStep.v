Require Import
  Coq.Program.Program
  Coq.Classes.Morphisms
  Coq.Lists.List
  Model
  CoSyntax.

Open Scope program_scope.
Open Scope list_scope.

Module LTLStep (S : StreamType).

Module Import LTL := LTL S.

Inductive Failed : Type :=
  | HitBottom
  | EndOfTrace
  | Rejected    (x : S.a)
  | BothFailed  (p q : Failed)
  | LeftFailed  (p : Failed)
  | RightFailed (q : Failed).

Inductive Result : Type :=
  | Failure  (e : Failed)
  | Continue (l : Formula)
  | Success.

Open Scope ltl_scope.

Definition and_result (f g : Result) : Result :=
  match f, g with
  | Failure e, _   => Failure (LeftFailed e)
  | _, Failure e   => Failure (RightFailed e)
  | Continue f',
    Continue g'    => Continue (f' ∧ g')
  | f', Success    => f'
  | Success, g'    => g'
  end.

Definition or_result (f g : Result) : Result :=
  match f, g with
  | Failure e1,
    Failure e2     => Failure (BothFailed e1 e2)
  | Success, _     => Success
  | _, Success     => Success
  | Continue f',
    Continue g'    => Continue (f' ∨ g')
  | Failure _, g'  => g'
  | f', Failure _  => f'
  end.

Fixpoint step (l : Formula) (x : S.a) : Result :=
  match l with
  | Top               => Success
  | Bottom            => Failure HitBottom
  | Examine v         => step (v x) x
  | And p q           => and_result (step p x) (step q x)
  | Or p q            => or_result (step p x) (step q x)
  | Next p            => Continue p
  | Until p q         => or_result  (step q x) (and_result (step p x) (Continue (Until p q)))
  | Release p q       => and_result (step q x) (or_result  (step p x) (Continue (Release p q)))
  | Always p          => and_result (step p x) (Continue (Always p))
  | Eventually p      => or_result  (step p x) (Continue (Eventually p))
  | Wait p q          => or_result  (step q x) (and_result (step p x) (Continue (Wait p q)))
  | StrongRelease p q => and_result (step q x) (or_result (step p x) (Continue (StrongRelease p q)))
  end.

Fixpoint step (l : Formula) (x : S.a) : Result :=
  match l with
  | Top               => Success
  | Bottom            => Failure HitBottom
  | Examine v         => step (v x) x
  | And p q           => and_result (step p x) (step q x)
  | Or p q            => or_result (step p x) (step q x)
  | Next p            => Continue p
  | Until p q         => or_result  (step q x) (and_result (step p x) (Continue (Until p q)))
  | Release p q       => and_result (step q x) (or_result  (step p x) (Continue (Release p q)))
  | Always p          => and_result (step p x) (Continue (Always p))
  | Eventually p      => or_result  (step p x) (Continue (Eventually p))
  | Wait p q          => or_result  (step q x) (and_result (step p x) (Continue (Wait p q)))
  | StrongRelease p q => and_result (step q x) (or_result (step p x) (Continue (StrongRelease p q)))
  end.

Definition step (m : Result) (x : S.a) : Result :=
  match m with
  | Continue l => step l (Some x)
  | r => r
  end.

Function run (m : Formula) (xs : list S.a) : Result :=
  match xs with
  | nil     => step m None
  | x :: xs =>
    match step m (Some x) with
    | Continue l => run l xs
    | Failure e  => Failure e
    | Success    => Success
    end
  end.

Definition passes (r : Result) : Prop :=
  match r with
  | Failure e  => False
  | Continue _ => True
  | Success    => True
  end.

Definition passes_equiv (p q : Result) : Prop := passes p <-> passes q.
Arguments passes_equiv p q /.

#[global]
Program Instance Equivalence_passes_equiv : Equivalence passes_equiv.
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

Lemma run_and p q s :
  passes (run (p ∧ q) s) <-> passes (run p s) /\ passes (run q s).
Proof.
  unfold and.
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (step p None); simpl in *; intuition.
    + destruct (step q None); simpl in *; intuition.
      destruct (step p None); simpl in *; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition.
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      now specialize (IHs _ _ H).
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      now specialize (IHs _ _ H).
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (step p None) eqn:?; simpl in *; intuition;
      destruct (step q None) eqn:?; simpl in *; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
Qed.

Lemma run_or p q s :
  passes (run (p ∨ q) s) <-> passes (run p s) \/ passes (run q s).
Proof.
  unfold and.
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (step p None); simpl in *; intuition;
      destruct (step q None); simpl in *; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (step p None) eqn:?; simpl in *; intuition;
      destruct (step q None) eqn:?; simpl in *; intuition.
    + destruct (step p None) eqn:?; simpl in *; intuition;
      destruct (step q None) eqn:?; simpl in *; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
Qed.

Lemma run_next p x xs :
  passes (run (Next p) (x :: xs)) <-> passes (run p xs).
Proof. now induction xs; intuition. Qed.

Lemma run_until p q s :
  passes (run (Until p q) s) <->
  let fix go s :=
      match s with
      | nil     => passes (run q s)
      | _ :: xs => passes (run q s) \/ (passes (run p s) /\ go xs)
      end in go s.
Proof.
  unfold and.
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    destruct (step p (Some a)) eqn:?; simpl in *; intuition;
    destruct (step q (Some a)) eqn:?; simpl in *; intuition.
    + rewrite run_and in H.
      now firstorder.
    + rewrite run_or, run_and in H.
      now firstorder.
    + now firstorder.
    + rewrite run_or in H.
      now firstorder.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    destruct (step p (Some a)) eqn:?; simpl in *; intuition;
    destruct (step q (Some a)) eqn:?; simpl in *; intuition.
    + rewrite run_or, run_and.
      now firstorder.
    + rewrite run_or.
      now firstorder.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_and.
        now firstorder.
      * rewrite run_or, run_and.
        now firstorder.
      * rewrite run_or.
        now firstorder.
Qed.

Lemma run_wait p q s :
  passes (run (Wait p q) s) <->
  let fix go s :=
      match s with
      | nil     => passes (run q s) \/ passes (run p s)
      | _ :: xs => passes (run q s) \/ (passes (run p s) /\ go xs)
      end in go s.
Proof.
  unfold and.
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (step p None) eqn:?; simpl in *; intuition;
      destruct (step q None) eqn:?; simpl in *; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_and in H.
        now firstorder.
      * rewrite run_or, run_and in H.
        now firstorder.
      * now firstorder.
      * rewrite run_or in H.
        now firstorder.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (step p None) eqn:?; simpl in *; intuition;
      destruct (step q None) eqn:?; simpl in *; intuition.
    + destruct (step p None) eqn:?; simpl in *; intuition;
      destruct (step q None) eqn:?; simpl in *; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_or, run_and.
        now firstorder.
      * rewrite run_or.
        now firstorder.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_and.
        now firstorder.
      * rewrite run_or, run_and.
        now firstorder.
      * rewrite run_or.
        now firstorder.
Qed.

Lemma run_always p s :
  passes (run (Always p) s) <->
  let fix go s :=
      match s with
      | nil     => passes (run p s)
      | _ :: xs => passes (run p s) /\ go xs
      end in go s.
Proof.
  unfold and.
  split; intros.
  - generalize dependent p.
    induction s; simpl; intros; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition.
      rewrite run_and in H.
      now firstorder.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_and in H.
        now firstorder.
      * now firstorder.
  - generalize dependent p.
    induction s; simpl; intros; intuition.
    destruct (step p (Some a)) eqn:?; simpl in *; intuition.
    rewrite run_and.
    now firstorder.
Qed.

Lemma run_eventually p s :
  passes (run (Eventually p) s) <->
  let fix go s :=
      match s with
      | nil     => passes (run p s)
      | _ :: xs => passes (run p s) \/ go xs
      end in go s.
Proof.
  unfold and.
  split; intros.
  - generalize dependent p.
    induction s; simpl; intros; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition.
      * now firstorder.
      * rewrite run_or in H.
        now firstorder.
  - generalize dependent p.
    induction s; simpl; intros; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition.
      rewrite run_or.
      now firstorder.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition.
      rewrite run_or.
      now firstorder.
Qed.

Lemma run_release p q s :
  passes (run (Release p q) s) <->
  let fix go s :=
      match s with
      | nil     => passes (run q s)
      | _ :: xs => passes (run q s) /\ (passes (run p s) \/ go xs)
      end in go s.
Proof.
  unfold and.
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    destruct (step p (Some a)) eqn:?; simpl in *; intuition;
    destruct (step q (Some a)) eqn:?; simpl in *; intuition.
    + rewrite run_and in H.
      now firstorder.
    + rewrite run_and, run_or in H.
      now firstorder.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_and in H.
        now firstorder.
      * now firstorder.
      * rewrite run_and, run_or in H.
        now firstorder.
      * rewrite run_or in H.
        now firstorder.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    destruct (step p (Some a)) eqn:?; simpl in *; intuition;
    destruct (step q (Some a)) eqn:?; simpl in *; intuition.
    + rewrite run_and, run_or.
      now firstorder.
    + rewrite run_or.
      now firstorder.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_and.
        now firstorder.
      * rewrite run_and, run_or.
        now firstorder.
      * rewrite run_or.
        now firstorder.
Qed.

Lemma run_strong_release p q s :
  passes (run (StrongRelease p q) s) <->
  let fix go s :=
      match s with
      | nil     => passes (run q s) /\ passes (run p s)
      | _ :: xs => passes (run q s) /\ (passes (run p s) \/ go xs)
      end in go s.
Proof.
  unfold and.
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (step p None) eqn:?; simpl in *; intuition;
      destruct (step q None) eqn:?; simpl in *; intuition.
    + destruct (step p None) eqn:?; simpl in *; intuition;
      destruct (step q None) eqn:?; simpl in *; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_and in H.
        now firstorder.
      * rewrite run_and, run_or in H.
        now firstorder.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_and in H.
        now firstorder.
      * now firstorder.
      * rewrite run_and, run_or in H.
        now firstorder.
      * rewrite run_or in H.
        now firstorder.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (step p None) eqn:?; simpl in *; intuition;
      destruct (step q None) eqn:?; simpl in *; intuition.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_and, run_or.
        now firstorder.
      * rewrite run_or.
        now firstorder.
    + destruct (step p (Some a)) eqn:?; simpl in *; intuition;
      destruct (step q (Some a)) eqn:?; simpl in *; intuition.
      * rewrite run_and.
        now firstorder.
      * rewrite run_and, run_or.
        now firstorder.
      * rewrite run_or.
        now firstorder.
Qed.

Lemma run_correct (l : Formula) (s : list S.a) :
  matches l s <-> passes (run l s).
Proof.
  generalize dependent s.
  induction l; intros.
  - now induction s.
  - now induction s.
  - induction s; intuition.
    + now specialize (proj1 (H _ _) H0).
    + now apply H, H0.
    + now specialize (proj1 (H _ _) H2).
    + now apply H, H2.
  - split; intros.
      destruct H.
      specialize (proj1 (IHl1 _) H); intros; clear IHl1 H.
      specialize (proj1 (IHl2 _) H0); intros; clear IHl2 H0.
      now apply run_and.
    apply run_and in H.
    now firstorder.
  - split; intros.
      destruct H.
        specialize (proj1 (IHl1 _) H); intros; clear IHl1 H.
        apply run_or.
        now left.
      specialize (proj1 (IHl2 _) H); intros; clear IHl2 H.
      apply run_or.
      now right.
    apply run_or in H.
    now firstorder.
  - split; intros;
    induction s; intuition.
    + now apply IHl in H.
    + now apply IHl in H.
    + now apply IHl.
    + now apply IHl.
  - split; intros.
      apply run_until.
      simpl.
      now induction s; firstorder.
    apply run_until in H.
    now induction s; firstorder.
  - split; intros.
      apply run_release.
      simpl.
      now induction s; firstorder.
    apply run_release in H.
    now induction s; firstorder.
  - split; intros.
      apply run_always.
      simpl.
      now induction s; firstorder.
    apply run_always in H.
    now induction s; firstorder.
  - split; intros.
      apply run_eventually.
      simpl.
      now induction s; firstorder.
    apply run_eventually in H.
    now induction s; firstorder.
  - split; intros.
      apply run_wait.
      simpl.
      now induction s; firstorder.
    apply run_wait in H.
    now induction s; firstorder.
  - split; intros.
      apply run_strong_release.
      simpl.
      now induction s; firstorder.
    apply run_strong_release in H.
    now induction s; firstorder.
Qed.

(*
Section Examples.

Import ListNotations.

Open Scope list_scope.

Goal passes _ (run _ (□ (num 3 ⇒ X (num 4))) [2; 3; 4]).
  simpl.
Abort.

Goal passes _ (run _ (□ (num 3 ⇒ ◇ (num 8))) [1; 2; 3; 4; 5; 6; 7; 8; 9]).
  simpl.
Abort.

End Examples.
*)

End LTLStep.
