Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.Classes.Morphisms
  Coq.Lists.List
  CDS4LTL.Model.

Open Scope program_scope.
Open Scope list_scope.

Module LTLStep.

Module Import LTL := LTL.

Section Step.

Context {a : Type}.

(** This data type encodes the syntax of LTL in Positive Normal Form (PNF). *)
Inductive Formula : Type :=
  | Top
  | Bottom
  | Examine       (v   : option a -> Formula)
  | And           (p q : Formula)
  | Or            (p q : Formula)
  | Next          (p   : Formula)
  | Until         (p q : Formula)
  | Wait          (p q : Formula)
  | Always        (p   : Formula)
  | Eventually    (p   : Formula)
  | Release       (p q : Formula)
  | StrongRelease (p q : Formula).

Inductive Failed : Type :=
  | HitBottom
  | EndOfTrace
  | Rejected    (x : a)
  | BothFailed  (p q : Failed)
  | LeftFailed  (p : Failed)
  | RightFailed (q : Failed).

Inductive Result : Type :=
  | Failure  (e : Failed)
  | Continue (l : Formula)
  | Success.

Open Scope ltl_scope.

Fixpoint negate (l : Formula) : Formula :=
  match l with
  | Top               => Bottom
  | Bottom            => Top
  | Examine v         => Examine (negate ∘ v)
  | And p q           => Or (negate p) (negate q)
  | Or p q            => And (negate p) (negate q)
  | Next p            => Next (negate p)
  | Until p q         => Release (negate p) (negate q)
  | Wait p q          => StrongRelease (negate p) (negate q)
  | Always p          => Eventually (negate p)
  | Eventually p      => Always (negate p)
  | Release p q       => Until (negate p) (negate q)
  | StrongRelease p q => Wait (negate p) (negate q)
  end.

Fixpoint size (p : Formula) : nat :=
  match p with
  | Top               => 1
  | Bottom            => 1
  | Examine v         => 1
  | And p q           => 1 + size p + size q
  | Or p q            => 1 + size p + size q
  | Next p            => 1 + size p
  | Until p q         => 1 + size p + size q
  | Wait p q          => 1 + size p + size q
  | Always p          => 1 + size p
  | Eventually p      => 1 + size p
  | Release p q       => 1 + size p + size q
  | StrongRelease p q => 1 + size p + size q
  end.

Definition and_result (f g : Result) : Result :=
  match f, g with
  | Failure e, _   => Failure (LeftFailed e)
  | _, Failure e   => Failure (RightFailed e)
  | Continue f',
    Continue g'    => Continue (And f' g')
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
    Continue g'    => Continue (Or f' g')
  | Failure _, g'  => g'
  | f', Failure _  => f'
  end.

Fixpoint compile (l : Formula) : option a -> Result := fun mx =>
  match l with
  | Top    => Success
  | Bottom => Failure HitBottom

  | Examine v =>
    match mx with
    | None   => compile (v None) None
    | Some x => compile (v (Some x)) (Some x)
    end

  | And p q => and_result (compile p mx) (compile q mx)
  | Or p q  => or_result (compile p mx) (compile q mx)

  | Next p   =>
    match mx with
    | None   => compile p None
    | Some _ => Continue p
    end

  | Until p q =>
    match mx with
    | None   => compile q None
    | Some x => or_result (compile q mx)
                          (and_result (compile p mx) (Continue (Until p q)))
    end

  | Release p q =>
    match mx with
    | None   => compile q None
    | Some x => and_result (compile q mx)
                           (or_result (compile p mx) (Continue (Release p q)))
    end

  | Always p =>
    match mx with
    | None   => compile p None
    | Some x => and_result (compile p mx) (Continue (Always p))
    end

  | Eventually p =>
    match mx with
    | None   => compile p None
    | Some x => or_result (compile p mx) (Continue (Eventually p))
    end

  | Wait p q =>
    match mx with
    | None   => or_result (compile q None) (compile p None)
    | Some x => or_result (compile q mx)
                          (and_result (compile p mx) (Continue (Wait p q)))
    end

  | StrongRelease p q =>
    match mx with
    | None   => and_result (compile q None) (compile p None)
    | Some x => and_result (compile q mx)
                           (or_result (compile p mx) (Continue (StrongRelease p q)))
    end
  end.

Definition step (m : Result) (x : a) : Result :=
  match m with
  | Continue l => compile l (Some x)
  | r => r
  end.

Fixpoint run (m : Formula) (xs : list a) : Result :=
  match xs with
  | nil     => compile m None
  | x :: xs =>
    match compile m (Some x) with
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
  passes (run (And p q) s) <-> passes (run p s) /\ passes (run q s).
Proof.
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (compile p None); simpl in *; intuition.
    + destruct (compile q None); simpl in *; intuition.
      destruct (compile p None); simpl in *; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition.
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
      now specialize (IHs _ _ H).
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
      now specialize (IHs _ _ H).
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (compile p None) eqn:?; simpl in *; intuition;
      destruct (compile q None) eqn:?; simpl in *; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
Qed.

Lemma run_or p q s :
  passes (run (Or p q) s) <-> passes (run p s) \/ passes (run q s).
Proof.
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (compile p None); simpl in *; intuition;
      destruct (compile q None); simpl in *; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (compile p None) eqn:?; simpl in *; intuition;
      destruct (compile q None) eqn:?; simpl in *; intuition.
    + destruct (compile p None) eqn:?; simpl in *; intuition;
      destruct (compile q None) eqn:?; simpl in *; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
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
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
    destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
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
    destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
    destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
    + rewrite run_or, run_and.
      now firstorder.
    + rewrite run_or.
      now firstorder.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
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
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (compile p None) eqn:?; simpl in *; intuition;
      destruct (compile q None) eqn:?; simpl in *; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
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
    + destruct (compile p None) eqn:?; simpl in *; intuition;
      destruct (compile q None) eqn:?; simpl in *; intuition.
    + destruct (compile p None) eqn:?; simpl in *; intuition;
      destruct (compile q None) eqn:?; simpl in *; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
      * rewrite run_or, run_and.
        now firstorder.
      * rewrite run_or.
        now firstorder.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
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
  split; intros.
  - generalize dependent p.
    induction s; simpl; intros; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition.
      rewrite run_and in H.
      now firstorder.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition.
      * rewrite run_and in H.
        now firstorder.
      * now firstorder.
  - generalize dependent p.
    induction s; simpl; intros; intuition.
    destruct (compile p (Some a0)) eqn:?; simpl in *; intuition.
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
  split; intros.
  - generalize dependent p.
    induction s; simpl; intros; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition.
      * now firstorder.
      * rewrite run_or in H.
        now firstorder.
  - generalize dependent p.
    induction s; simpl; intros; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition.
      rewrite run_or.
      now firstorder.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition.
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
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
    destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
    + rewrite run_and in H.
      now firstorder.
    + rewrite run_and, run_or in H.
      now firstorder.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
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
    destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
    destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
    + rewrite run_and, run_or.
      now firstorder.
    + rewrite run_or.
      now firstorder.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
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
  split; intros.
  - generalize dependent p.
    generalize dependent q.
    induction s; simpl; intros; intuition.
    + destruct (compile p None) eqn:?; simpl in *; intuition;
      destruct (compile q None) eqn:?; simpl in *; intuition.
    + destruct (compile p None) eqn:?; simpl in *; intuition;
      destruct (compile q None) eqn:?; simpl in *; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
      * rewrite run_and in H.
        now firstorder.
      * rewrite run_and, run_or in H.
        now firstorder.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
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
    + destruct (compile p None) eqn:?; simpl in *; intuition;
      destruct (compile q None) eqn:?; simpl in *; intuition.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
      * rewrite run_and, run_or.
        now firstorder.
      * rewrite run_or.
        now firstorder.
    + destruct (compile p (Some a0)) eqn:?; simpl in *; intuition;
      destruct (compile q (Some a0)) eqn:?; simpl in *; intuition.
      * rewrite run_and.
        now firstorder.
      * rewrite run_and, run_or.
        now firstorder.
      * rewrite run_or.
        now firstorder.
Qed.

(*
Lemma run_correct (l : Formula) (s : list a) :
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
      apply run_wait.
      simpl.
      now induction s; firstorder.
    apply run_wait in H.
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
      apply run_release.
      simpl.
      now induction s; firstorder.
    apply run_release in H.
    now induction s; firstorder.
  - split; intros.
      apply run_strong_release.
      simpl.
      now induction s; firstorder.
    apply run_strong_release in H.
    now induction s; firstorder.
Qed.
*)

End Step.

End LTLStep.

Require Import Coq.Arith.PeanoNat.

Module StepExamples.

Module Import S := LTLStep.
Import S.LTL.

Import ListNotations.

#[global]
Declare Scope boolean_scope.
Bind Scope boolean_scope with Formula.
Delimit Scope boolean_scope with boolean.
Open Scope boolean_scope.

Notation "¬ p"    := (negate p)      (at level 75, right associativity) : boolean_scope.
Infix    "∨"      := Or              (at level 85, right associativity) : boolean_scope.
Notation "p ⇒ q"  := (¬ p ∨ q)       (at level 86, right associativity) : boolean_scope.
Notation "⊤"      := True            (at level 0, no associativity) : boolean_scope.
Notation "⊥"      := False           (at level 0, no associativity) : boolean_scope.
Infix    "∧"      := And             (at level 80, right associativity) : boolean_scope.
(* Infix    "⟹"     := implies         (at level 99, right associativity) : boolean_scope. *)
(* Infix    "≈"      := equivalent      (at level 90, no associativity) : boolean_scope. *)

#[global]
Declare Scope ltl_scope.
Bind Scope ltl_scope with Formula.
Delimit Scope ltl_scope with ltl.
Open Scope boolean_scope.
Open Scope ltl_scope.

Notation "◯ p"       := (Next p)             (at level 75, right associativity) : ltl_scope.
Notation "◇ p"       := (Eventually p)       (at level 75, right associativity) : ltl_scope.
Notation "□ p"       := (Always p)           (at level 75, right associativity) : ltl_scope.
Notation "p 'U' q"   := (Until p q)          (at level 79, right associativity) : ltl_scope.
Notation "p 'W' q"   := (Wait p q)           (at level 79, right associativity) : ltl_scope.
Notation "p 'R' q"   := (Release p q)        (at level 79, right associativity) : ltl_scope.
Notation "p 'M' q"   := (StrongRelease p q) (at level 79, right associativity) : ltl_scope.
Notation "'Λ' x , p" := (Examine (λ x , p))  (at level 97, no associativity) : ltl_scope.

Open Scope ltl_scope.

Definition num (n : nat) : @Formula nat :=
  Λ x, match x with
       | Some x => if x =? n then Top else Bottom
       | None => Bottom
       end.

Definition if_then {a : Type} (p : a -> bool) (f : a -> Formula) :=
  Λ x, match x with
       | Some x => if p x then f x else Top
       | None => Top
       end.

Fixpoint series {a : Type} (l : list (@Formula a)) : @Formula a :=
  match l with
  | nil => Top
  | x :: nil => x
  | x :: xs => x ∧ Next (series xs)
  end.

Example ex_match_query  :
  passes (run (num 1 ∧ ◯ (num 2)) [1; 2]).
Proof. constructor. Qed.

Example ex_match_series :
  passes (run (series [num 1; num 2]) [1; 2]).
Proof. constructor. Qed.

Example ex_match_sample1 :
  passes (run (◇ (num 3 ⇒ ◇ (num 8))) [1; 2; 3; 4; 5; 6; 7; 8; 9]).
Proof. constructor. Qed.

Example ex_match_sample2 :
  passes (run (◇ (if_then (λ n, n =? 3) (λ n, ◇ (num (n + 5)))))
              [1; 2; 3; 4; 5; 6; 7; 8; 9]).
Proof. constructor. Qed.

End StepExamples.
