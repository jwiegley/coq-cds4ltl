Set Warnings "-notation-overridden".

Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Coq.Lists.List
  Coq.Classes.Morphisms
  Coq.Logic.Classical
  FunInd
  Model
  Stream
  Bool
  MinLTL
  LTL.

Open Scope program_scope.
Open Scope list_scope.

Import ListNotations.

Module LTLSyntax (S : StreamType).

(** This data type encodes the syntax of LTL in Positive Normal Form (PNF). *)
Inductive Formula : Type :=
  | Top
  | Bottom
  | Examine       (v   : option S.a -> Formula)
  | And           (p q : Formula)
  | Or            (p q : Formula)
  | Next          (p   : Formula)
  | Until         (p q : Formula)
  | Wait          (p q : Formula)
  | Always        (p   : Formula)
  | Eventually    (p   : Formula)
  | Release       (p q : Formula)
  | StrongRelease (p q : Formula).

Function negate (l : Formula) : Formula :=
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

(** Prune out any instances of Top or Bottom *)
Function prune (l : Formula) : Formula :=
  match l with
  | Top               => l
  | Bottom            => l
  | Examine v         => l
  | And p q           => match prune p with
                         | Top => prune q
                         | _   =>
                           match prune q with
                           | Top => prune p
                           | _   => And (prune p) (prune q)
                           end
                         end
  | Or p q            => match prune p with
                         | Bottom => prune q
                         | _      =>
                           match prune q with
                           | Bottom => prune p
                           | _      => Or (prune p) (prune q)
                           end
                         end
  | Next p            => Next (prune p)
  | Until p q         => Until (prune p) (prune q)
  | Wait p q          => Wait (prune p) (prune q)
  | Always p          => Always (prune p)
  | Eventually p      => Eventually (prune p)
  | Release p q       => Release (prune p) (prune q)
  | StrongRelease p q => StrongRelease (prune p) (prune q)
  end.

Fixpoint matches (l : Formula) (s : list S.a) {struct l} : Prop :=
  match l with
  | Top    => True
  | Bottom => False

  | Examine v =>
    match s with
    | nil    => matches (v None) s
    | x :: _ => matches (v (Some x)) s
    end

  | And p q => matches p s /\ matches q s
  | Or p q  => matches p s \/ matches q s

  | Next p =>
    match s with
    | nil     => matches p nil
    | x :: xs => matches p xs
    end

  | Until p q =>
    let fix go s :=
        match s with
        | nil     => matches q s
        | _ :: xs => matches q s \/ (matches p s /\ go xs)
        end in go s

  | Wait p q =>
    let fix go s :=
        match s with
        | nil     => matches q s \/ matches p s
        | _ :: xs => matches q s \/ (matches p s /\ go xs)
        end in go s

  | Always p =>
    let fix go s :=
        match s with
        | nil     => matches p s
        | _ :: xs => matches p s /\ go xs
        end in go s

  | Eventually p =>
    let fix go s :=
        match s with
        | nil     => matches p s
        | _ :: xs => matches p s \/ go xs
        end in go s

  | Release p q =>
    let fix go s :=
        match s with
        | nil     => matches q s
        | _ :: xs => matches q s /\ (matches p s \/ go xs)
        end in go s

  | StrongRelease p q =>
    let fix go s :=
        match s with
        | nil     => matches q s /\ matches p s
        | _ :: xs => matches q s /\ (matches p s \/ go xs)
        end in go s
  end.

Inductive Matches : Formula -> list S.a -> Type :=
  | MatchTop x xs : Matches Top (x :: xs)

  | MatchBottom p :
      (* The following operators cannot match at the end of a finite input,
         meaning for example that you cannot have an [◇ p] that does not
         eventually match [p]. *)
      match prune p with
      | Top               => False
      | Next _            => False
      | Until _ _         => False
      | Eventually _      => False
      | StrongRelease _ _ => False
      | _                 => True
      end ->
      Matches p []

  | MatchExamineEnd v :
      Matches (v None) [] -> Matches (Examine v) []
  | MatchExamine v x xs :
      Matches (v (Some x)) (x :: xs) -> Matches (Examine v) (x :: xs)

  | MatchAnd p q s :
      Matches p s -> Matches q s -> Matches (And p q) s

  | MatchOrLeft p q s :
      Matches p s -> Matches (Or p q) s
  | MatchOrRight p q s :
      Matches q s -> Matches (Or p q) s

  | MatchNext p x xs :
      Matches p xs -> Matches (Next p) (x :: xs)

  | MatchUntilStop p q s :
      Matches q s ->
      Matches (Until p q) s
  | MatchUntilFwd p q x xs :
      Matches p (x :: xs) ->
      Matches (Until p q) xs ->
      Matches (Until p q) (x :: xs)

  | MatchWaitStop p q s :
      Matches q s ->
      Matches (Wait p q) s
  | MatchWaitFwd p q x xs :
      Matches p (x :: xs) ->
      Matches (Wait p q) xs ->
      Matches (Wait p q) (x :: xs)

  | MatchAlways p x xs :
      Matches p (x :: xs) ->
      Matches (Always p) xs ->
      Matches (Always p) (x :: xs)

  | MatchEventuallyStop p s :
      Matches p s ->
      Matches (Eventually p) s
  | MatchEventuallyFwd p x xs :
      Matches (Eventually p) xs ->
      Matches (Eventually p) (x :: xs)

  | MatchReleaseStop p q s :
      Matches q s ->
      Matches p s ->
      Matches (Release p q) s
  | MatchReleaseFwd p q x xs :
      Matches q (x :: xs) ->
      Matches (Release p q) xs ->
      Matches (Release p q) (x :: xs)

  | MatchStrongReleaseStop p q s :
      Matches q s ->
      Matches p s ->
      Matches (StrongRelease p q) s
  | MatchStrongReleaseFwd p q x xs :
      Matches q (x :: xs) ->
      Matches (StrongRelease p q) xs ->
      Matches (StrongRelease p q) (x :: xs).

Import EqNotations.

Fixpoint check (l : Formula) (s : list S.a) : option (Matches l s) :=
  match l with
  | Top    =>
    match s with
    | nil => None
    | x :: xs => Some (MatchTop x xs)
    end
  | Bottom => None

  | Examine v =>
    match s as s' return s = s' -> _ with
    | nil => fun _ =>
      match check (v None) nil with
      | Some r => Some (MatchExamineEnd v r)
      | None   => None
      end
    | x :: xs => fun Heqe : s = x :: xs =>
      match check (v (Some x)) s with
      | Some r => Some (MatchExamine v x xs (rew Heqe in r))
      | None   => None
      end
    end eq_refl

  | And p q =>
    match check p s with
    | Some r =>
      match check q s with
      | Some t => Some (MatchAnd p q s r t)
      | None   => None
      end
    | None   => None
    end

  | Or p q  =>
    match check p s with
    | Some r => Some (MatchOrLeft p q s r)
    | None   =>
      match check q s with
      | Some t => Some (MatchOrRight p q s t)
      | None   => None
      end
    end

  | Next p =>
    match s with
    | nil => None
    | x :: xs =>
      match check p xs with
      | Some r => Some (MatchNext p x xs r)
      | None   => None
      end
    end

  | Until p q =>
    let fix go s : option (Matches (Until p q) s) :=
        match check q s with
        | Some r  => Some (MatchUntilStop p q s r)
        | None =>
          match s as s' return s = s' -> _ with
          | nil => fun _ => None
          | x :: xs => fun Heqe : s = x :: xs =>
            match check p s with
            | Some r =>
              match go xs with
              | Some t => Some (MatchUntilFwd p q x xs (rew Heqe in r) t)
              | None => None
              end
            | None => None
            end
          end eq_refl
        end in go s

  | Wait p q =>
    let fix go s : option (Matches (Wait p q) s) :=
        match s as s' return s = s' -> option (Matches (Wait p q) s') with
        | nil => fun _ => None
        | x :: xs =>
          fun Heqe : s = x :: xs =>
            match check q s with
            | Some r  => Some (rew Heqe in MatchWaitStop p q s r)
            | None =>
              match check p s with
              | Some r =>
                match xs as xs' return xs = xs' -> option (Matches (Wait p q) (x :: xs')) with
                | nil =>
                  fun Heqe2 : xs = nil =>
                    None
                    (* Some (MatchWaitEnd *)
                    (*         p q x (rew [fun z => Matches p (x :: z)] Heqe2 *)
                    (*                 in rew Heqe in r)) *)
                | y :: ys =>
                  fun Heqe2 : xs = y :: ys =>
                    match go xs with
                    | Some t => Some (rew [fun z => Matches (Wait p q) (x :: z)] Heqe2
                                       in MatchWaitFwd p q x xs (rew Heqe in r) t)
                    | None => None
                    end
                end eq_refl
              | None => None
              end
            end
        end eq_refl in go s

  | Always p =>
    let fix go s : option (Matches (Always p) s) :=
        match s as s' return s = s' -> option (Matches (Always p) s') with
        | nil => fun _ => None
        | x :: xs =>
          fun Heqe : s = x :: xs =>
            match check p s with
            | Some r =>
              match xs as xs' return xs = xs' -> option (Matches (Always p) (x :: xs')) with
              | nil =>
                fun Heqe2 : xs = nil =>
                  None
                  (* Some (MatchAlwaysEnd *)
                  (*         p x (rew [fun z => Matches p (x :: z)] Heqe2 *)
                  (*               in rew Heqe in r)) *)
              | y :: ys =>
                fun Heqe2 : xs = y :: ys =>
                  match go xs with
                  | Some t => Some (rew [fun z => Matches (Always p) (x :: z)] Heqe2
                                     in MatchAlways p x xs (rew Heqe in r) t)
                  | None => None
                  end
              end eq_refl
            | None => None
            end
        end eq_refl in go s

  | Eventually p =>
    let fix go s : option (Matches (Eventually p) s) :=
        match s as s' return s = s' -> _ with
        | nil => fun _ => None
        | x :: xs => fun Heqe : s = x :: xs =>
          match check p s with
          | Some r => Some (MatchEventuallyStop p s r)
          | None =>
            match go xs with
            | Some t => Some (rew <- Heqe in MatchEventuallyFwd p x xs t)
            | None => None
            end
          end
        end eq_refl in go s

  | Release p q =>
    let fix go s : option (Matches (Release p q) s) :=
        match s as s' return s = s' -> option (Matches (Release p q) s') with
        | nil => fun _ => None
        | x :: xs =>
          fun Heqe : s = x :: xs =>
            match check q s with
            | Some r  =>
              match xs as xs' return xs = xs' -> option (Matches (Release p q) (x :: xs')) with
              | nil =>
                fun Heqe2 : xs = nil =>
                  None
                  (* Some (MatchReleaseEnd *)
                  (*         p q x (rew [fun z => Matches q (x :: z)] Heqe2 *)
                  (*                 in rew Heqe in r)) *)
              | y :: ys =>
                fun Heqe2 : xs = y :: ys =>
                  match check p s with
                  | Some t => Some (rew [fun z => Matches (Release p q) (x :: z)] Heqe2
                                     in rew Heqe in MatchReleaseStop p q s r t)
                  | None =>
                    match go xs with
                    | Some t => Some (rew [fun z => Matches (Release p q) (x :: z)] Heqe2
                                       in MatchReleaseFwd p q x xs (rew Heqe in r) t)
                    | None => None
                    end
                  end
              end eq_refl
            | None => None
            end
        end eq_refl in go s

  | StrongRelease p q =>
    let fix go s : option (Matches (StrongRelease p q) s) :=
        match s as s' return s = s' -> _ with
        | nil => fun _ => None
        | x :: xs => fun Heqe : s = x :: xs =>
          match check q s with
          | Some r  =>
            match check p s with
            | Some t => Some (MatchStrongReleaseStop p q s r t)
            | None =>
              match go xs with
              | Some t => Some (rew <- Heqe in
                                   MatchStrongReleaseFwd p q x xs (rew Heqe in r) t)
              | None => None
              end
            end
          | None => None
          end
        end eq_refl in go s
  end.

Ltac inv H := inversion H; subst; clear H.

Theorem check_matches l s x : check l s = Some x -> matches l s.
Proof.
  intros.
  generalize dependent s.
  induction l; simpl; intros.
  + destruct s; inv H.
    now constructor.
  + now inv H.
  + destruct s; inv H0.
    * destruct (check (v None) []) eqn:Heqe; inv H2.
      now intuition eauto.
    * destruct (check (v (Some a)) (a :: s)) eqn:Heqe; inv H2.
      now intuition eauto.
  + destruct (check l1 s) eqn:Heqe1; inv H.
    destruct (check l2 s) eqn:Heqe2; inv H1.
    now split; intuition eauto.
  + destruct (check l1 s) eqn:Heqe1; inv H.
    * now left; intuition eauto.
    * destruct (check l2 s) eqn:Heqe2; inv H1.
      now right; intuition eauto.
  + destruct s; inv H.
    destruct (check l s) eqn:Heqe; inv H1.
    now intuition eauto.
  + induction s.
    * destruct (check l2 []) eqn:Heqe2; inv H.
      now intuition eauto.
    * destruct (check l2 (a :: s)) eqn:Heqe2; inv H.
      ** now left; intuition eauto.
      ** destruct (check l1 (a :: s)) eqn:Heqe1; inv H1.
         destruct (_ s); inv H0.
         right; intuition eauto.
         now eapply IHs; eauto.
  + induction s.
    * destruct (check l2 []) eqn:Heqe2; inv H.
    * destruct (check l2 (a :: s)) eqn:Heqe2; inv H.
      ** now left; intuition eauto.
      ** destruct (check l1 (a :: s)) eqn:Heqe1; inv H1.
         destruct (_ s); inv H0.
         *** right; intuition eauto.
             now eapply IHs; eauto.
         *** right.
             split.
             **** now intuition eauto.
             **** now destruct s; inv H1.
  + induction s.
    * now inv H.
    * destruct (check l (a :: s)) eqn:Heqe; inv H.
      split.
      ** now intuition eauto.
      ** destruct (_ s).
         *** now eapply IHs; eauto.
         *** destruct s.
             **** now inv H1.
             **** now inv H1.
  + induction s.
    * now inv H.
    * destruct (check l (a :: s)) eqn:Heqe; inv H.
      ** now left; intuition eauto.
      ** right.
         destruct (_ s).
         *** now eapply IHs; eauto.
         *** now inv H1.
  + induction s.
    * now inv H.
    * destruct (check l2 (a :: s)) eqn:Heqe2; inv H.
      destruct (check l1 (a :: s)) eqn:Heqe1; inv H1.
      ** now intuition eauto.
      ** destruct (_ s); inv H0.
         *** intuition eauto.
             right; intuition eauto.
             now eapply IHs; eauto.
         *** split.
             **** now intuition eauto.
             **** now destruct s; inv H1.
  + induction s.
    * now inv H.
    * destruct (check l2 (a :: s)) eqn:Heqe2; inv H.
      destruct (check l1 (a :: s)) eqn:Heqe1; inv H1.
      ** now intuition eauto.
      ** destruct (_ s); inv H0.
         intuition eauto.
         right; intuition eauto.
         now eapply IHs; eauto.
Qed.

Definition impl  := fun p q => forall s, matches p s -> matches q s.
Definition equiv := fun p q => impl p q /\ impl q p.

#[local] Infix "⟹" := impl  (at level 99, right associativity).
#[local] Infix "≈"  := equiv (at level 90, no associativity).

Ltac induct :=
  try split; repeat intro; simpl in *;
  match goal with
    [ S : list S.a |- _ ] => induction S
  end; firstorder.

#[local] Obligation Tactic := induct.

Program Instance impl_reflexive : Reflexive impl.
Program Instance impl_transitive : Transitive impl.
Program Instance Equivalence_equiv : Equivalence equiv.

#[local] Obligation Tactic := program_simpl.

Program Instance equiv_respects_equiv :
  Proper (equiv ==> equiv ==> iff) equiv.
Next Obligation.
  split; repeat intro.
  - now rewrite <- H0, <- H1, <- H.
  - now rewrite H0, <- H1.
Qed.

Program Instance matches_respects_impl :
  Proper (impl ==> eq ==> Basics.impl) matches.
Next Obligation.
  repeat intro.
  subst; now apply H.
Qed.

Program Instance matches_respects_equiv :
  Proper (equiv ==> eq ==> iff) matches.
Next Obligation.
  split; repeat intro.
  - subst; now apply H.
  - subst; now apply H.
Qed.

#[local] Obligation Tactic := induct.

Program Instance And_respects_impl :
  Proper (impl ==> impl ==> impl) And.

Program Instance And_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) And.

Program Instance Or_respects_impl :
  Proper (impl ==> impl ==> impl) Or.

Program Instance Or_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) Or.

Program Instance Next_respects_impl :
  Proper (impl ==> impl) Next.

Program Instance Next_respects_equiv :
  Proper (equiv ==> equiv) Next.

Program Instance Until_respects_impl :
  Proper (impl ==> impl ==> impl) Until.

Program Instance Until_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) Until.

Program Instance Wait_respects_impl :
  Proper (impl ==> impl ==> impl) Wait.

Program Instance Wait_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) Wait.

Program Instance Always_respects_impl :
  Proper (impl ==> impl) Always.

Program Instance Always_respects_equiv :
  Proper (equiv ==> equiv) Always.

Program Instance Eventually_respects_impl :
  Proper (impl ==> impl) Eventually.

Program Instance Eventually_respects_equiv :
  Proper (equiv ==> equiv) Eventually.

Program Instance Release_respects_impl :
  Proper (impl ==> impl ==> impl) Release.

Program Instance Release_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) Release.

Program Instance StrongRelease_respects_impl :
  Proper (impl ==> impl ==> impl) StrongRelease.

Program Instance StrongRelease_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) StrongRelease.

Lemma matches_negate x s : matches (negate x) s <-> ~ matches x s.
Proof.
  split; intro.
  - intro.
    generalize dependent s.
    induction x; intros;
    induction s; simpl in *;
    now firstorder eauto.
  - generalize dependent s.
    induction x; intros;
    try (solve [simpl in *; intuition eauto]).
    + simpl negate.
      unfold Basics.compose.
      induction s;
      now simpl in *; firstorder.
    + simpl in *.
      apply not_and_or in H.
      now intuition.
    + simpl in *.
      now destruct s; intuition.
    + simpl negate.
      induction s.
        now simpl in *; intuition.
      simpl matches in H.
      apply not_or_and in H.
      destruct H.
      apply not_and_or in H0.
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        now simpl in *; intuition.
      simpl matches in H.
      apply not_or_and in H.
      destruct H.
      apply not_and_or in H0.
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        now simpl in *; intuition.
      simpl matches in H.
      apply not_and_or in H.
      destruct H;
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        now simpl in *; intuition.
      simpl matches in H.
      apply not_or_and in H.
      destruct H;
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        now simpl in *; intuition.
      simpl matches in H.
      apply not_and_or in H.
      destruct H;
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        simpl matches in H.
        apply not_and_or in H.
        now simpl in *; intuition.
      simpl matches in H.
      apply not_and_or in H.
      destruct H.
        now simpl in *; intuition.
      apply not_or_and in H.
      now simpl in *; intuition.
Qed.

Lemma negate_negate p : negate (negate p) ≈ p.
Proof.
  split; repeat intro;
  rewrite !matches_negate in *.
  - apply NNPP; intro.
    apply H; clear H; intro.
    apply H0; clear H0.
    generalize dependent s.
    induction p; simpl in *; intros;
    induction s; intuition auto.
  - intro.
    apply H0; clear H0.
    generalize dependent s;
    induction p; simpl in *; intros;
    induction s; intuition auto.
Qed.

Lemma matches_not_false {p s} : matches p s -> matches (negate p) s -> False.
Proof.
  intros.
  rewrite matches_negate in H0.
  contradiction.
Qed.

#[local] Obligation Tactic := program_simpl.

Program Instance negate_respects_impl : Proper (impl --> impl) negate | 1.
Next Obligation.
  repeat intro.
  apply matches_negate.
  apply matches_negate in H0.
  now firstorder.
Qed.

Lemma prune_correct l : prune l ≈ l.
Proof.
  apply prune_ind; simpl; intros; subst; intuition.
  - split; repeat intro; simpl; intuition.
    + rewrite <- H.
      now rewrite e0.
    + now rewrite <- H0.
    + simpl in H1.
      now rewrite H0.
  - split; repeat intro; simpl; intuition.
    + now rewrite <- H.
    + rewrite <- H0.
      now rewrite e1.
    + simpl in H2.
      now rewrite H1.
  - now rewrite H1, H2.
  - split; repeat intro; simpl; intuition.
    + right.
      now rewrite <- H0.
    + simpl in H1.
      destruct H1.
      * rewrite <- H, e0 in H1.
        contradiction.
      * now rewrite H0.
  - split; repeat intro; simpl; intuition.
    + left.
      now rewrite <- H1.
    + simpl in H2.
      destruct H2.
      * now rewrite H1.
      * rewrite <- H0, e1 in H2.
        contradiction.
  - now rewrite H1, H2.
  - now rewrite H.
  - now rewrite H, H0.
  - now rewrite H, H0.
  - now rewrite H.
  - now rewrite H.
  - now rewrite H, H0.
  - now rewrite H, H0.
Qed.

End LTLSyntax.

Module OptionStreamType (S : StreamType).

Definition a := option S.a.

End OptionStreamType.

Module LTL (S : StreamType) <: LinearTemporalLogicW <: LinearTemporalLogic.

Module AST := LTLSyntax S.
Import AST.

Module O := OptionStreamType S.
Module SL := StreamLTL O.
Module Import L   := LinearTemporalLogicFacts SL.
Module Import LW  := LinearTemporalLogicWFacts SL.
Module Import ML  := MinimalLinearTemporalLogicFacts SL.
Module Import BF  := ML.BF.
Module Import MBF := BF.MBF.
Import SL.

Fixpoint denote (l : Formula) : t :=
  match l with
  | Top               => ⊤
  | Bottom            => ⊥
  | Examine v         => λ s, denote (v (head s)) s
  | And p q           => denote p ∧ denote q
  | Or p q            => denote p ∨ denote q
  | Next p            => ◯ (denote p)
  | Until p q         => denote p U denote q
  | Wait p q          => denote p W denote q
  | Always p          => □ (denote p)
  | Eventually p      => ◇ (denote p)
  | Release p q       => denote p R denote q
  | StrongRelease p q => denote p M denote q
  end.

Definition t := Formula.

Theorem not_denote p : ¬ (denote p) ≈ denote (negate p).
Proof.
  induction p; simpl.
  - now rewrite not_true.
  - now rewrite not_false.
  - split; repeat intro; unfold Ensembles.In in *.
    + now apply H, H0.
    + apply H in H0.
      contradiction.
  - rewrite not_and.
    now rewrite IHp1, IHp2.
  - rewrite not_or.
    now rewrite IHp1, IHp2.
  - rewrite <- next_not.
    now rewrite IHp.
  - unfold release.
    rewrite <- !IHp1.
    rewrite <- !IHp2.
    rewrite and_comm.
    now rewrite <- law_173.
  - unfold strong_release.
    rewrite <- !IHp1.
    rewrite <- !IHp2.
    rewrite and_comm.
    rewrite <- not_until.
    unfold wait.
    rewrite always_def.
    rewrite evn_def.
    rewrite and_def.
    now rewrite not_not.
  - rewrite always_def.
    rewrite not_not.
    now rewrite IHp.
  - rewrite always_def.
    rewrite <- IHp.
    now rewrite not_not.
  - unfold release.
    rewrite not_swap.
    rewrite <- !IHp1.
    rewrite <- !IHp2.
    rewrite law_199.
    now rewrite and_comm.
  - unfold strong_release.
    rewrite and_comm.
    rewrite <- law_201.
    rewrite <- !IHp1.
    rewrite <- !IHp2.
    now rewrite not_not.
Qed.

Fixpoint project {A : Type} (xs : list A) : Stream (option A) :=
  match xs with
  | nil => constant None
  | cons x xs => Cons (Some x) (project xs)
  end.

Theorem denote_matches l s : matches l s <-> denote l (project s).
Proof.
  split; intros.
  - generalize dependent s.
    induction l; simpl; intros.
    + now constructor.
    + contradiction.
    + now destruct s; intuition.
    + now inv H; split; firstorder.
    + inv H.
      * now left; firstorder.
      * now right; firstorder.
    + now destruct s; firstorder.
    + induction s.
      * apply IHl2 in H.
        exists 0.
        intuition.
        lia.
      * destruct H.
        ** apply IHl2 in H.
           exists 0.
           intuition.
           lia.
        ** destruct H.
           apply IHl1 in H.
           apply IHs in H0; clear IHs.
           clear -H H0.
           inv H0.
           destruct H1.
           exists (S x).
           intuition.
           destruct i.
           *** exact H.
           *** apply H1; lia.
    + unfold wait.
      induction s.
      * destruct H.
        ** apply IHl2 in H.
           right.
           exists 0.
           intuition.
           lia.
        ** apply IHl1 in H.
           left.
           intro.
           now induction i.
      * destruct H.
        ** clear IHs.
           right.
           apply IHl2 in H.
           exists 0.
           intuition.
           lia.
        ** destruct H.
           apply IHl1 in H.
           apply IHs in H0; clear IHs.
           clear -H H0.
           inv H0.
           *** left.
               intro.
               induction i.
               **** exact H.
               **** now apply H1.
           *** inv H1.
               destruct H0.
               right.
               exists (S x).
               intuition.
               destruct i.
               **** exact H.
               **** apply H1; lia.
    + induction s.
      * apply IHl in H.
        intro.
        now induction i.
      * destruct H.
        apply IHl in H.
        apply IHs in H0; clear IHs.
        intro.
        now induction i; simpl.
    + induction s.
      * apply IHl in H.
        exists 0.
        exact H.
      * destruct H.
        ** exists 0.
           now firstorder.
        ** apply IHs in H; clear IHs.
           inv H.
           now exists (S x).
    + unfold release, wait.
      induction s.
      * apply IHl2 in H.
        left.
        intro.
        now induction i.
      * destruct H.
        destruct H0.
        ** clear IHs.
           right.
           apply IHl1 in H0.
           apply IHl2 in H.
           exists 0.
           split.
           *** now split.
           *** lia.
        ** apply IHl2 in H.
           apply IHs in H0; clear IHs.
           clear -H H0.
           inv H0.
           *** left.
               intro.
               induction i.
               **** exact H.
               **** now apply H1.
           *** inv H1.
               destruct H0.
               right.
               exists (S x).
               intuition.
               destruct i.
               **** exact H.
               **** apply H1; lia.
    + unfold strong_release.
      induction s.
      * destruct H.
        apply IHl1 in H0.
        apply IHl2 in H.
        exists 0.
        split.
        ** now split.
        ** lia.
      * destruct H.
        destruct H0.
        ** clear IHs.
           exists 0.
           apply IHl1 in H0.
           apply IHl2 in H.
           split.
           *** now split.
           *** lia.
        ** apply IHl2 in H.
           apply IHs in H0; clear IHs.
           clear -H H0.
           inv H0.
           inv H1.
           inv H0.
           exists (S x).
           split.
           *** now split.
           *** intros.
               induction i.
               **** exact H.
               **** apply H2; lia.
  - generalize dependent s.
    induction l; simpl; intros.
    + now constructor.
    + contradiction.
    + now destruct s; intuition.
    + now inv H; split; firstorder.
    + inv H.
      * now left; firstorder.
      * now right; firstorder.
    + now destruct s; firstorder.
    + induction s.
      * apply IHl2.
        inv H; destruct H0.
        simpl in *.
        clear -H.
        now induction x; simpl in H; auto.
      * inv H; destruct H0.
        destruct x.
        ** left.
           apply IHl2.
           exact H.
        ** right.
           split.
           *** apply IHl1.
               apply (H0 0).
               lia.
           *** apply IHs.
               exists x.
               simpl in H.
               intuition.
               apply (H0 (S i)).
               lia.
    + unfold wait in H.
      induction s.
      * inv H.
        ** right.
           apply IHl1.
           now apply (H0 0).
        ** inv H0.
           destruct H.
           destruct x; intuition.
           right.
           apply IHl1.
           apply (H0 0).
           lia.
      * inv H.
        ** right.
           split.
           *** apply IHl1.
               now apply (H0 0).
           *** apply IHs.
               left.
               intro.
               now apply (H0 (S i)).
        ** inv H0.
           destruct H.
           destruct x.
           *** left.
               now apply IHl2.
           *** right.
               split.
               **** apply IHl1.
                    apply (H0 0).
                    lia.
               **** apply IHs.
                    right.
                    exists x.
                    split; auto; intros.
                    apply (H0 (S i)).
                    lia.
    + induction s.
      * apply IHl.
        now apply (H 0).
      * split.
        ** apply IHl.
           now apply (H 0).
        ** apply IHs; clear IHs.
           intro.
           now apply (H (S i)).
    + induction s.
      * apply IHl.
        inv H.
        now induction x; auto.
      * inv H.
        destruct x.
        ** left.
           now apply IHl.
        ** right.
           apply IHs; clear IHs.
           now exists x.
    + admit.
    + admit.
Admitted.

Definition true           := Top.
Definition false          := Bottom.
Definition and            := And.
Definition or             := Or.
Definition not            := negate.
Definition implies        := impl.
Definition equivalent     := equiv.
Definition next           := Next.
Definition until          := Until.
Definition wait           := Wait.
Definition always         := Always.
Definition eventually     := Eventually.
Definition release        := Release.
Definition strong_release := StrongRelease.
Definition examine        := Examine.

Declare Scope boolean_scope.
Bind Scope boolean_scope with Formula.
Delimit Scope boolean_scope with boolean.
Open Scope boolean_scope.

Notation "¬ p"    := (not p)         (at level 75, right associativity) : boolean_scope.
Infix    "∨"      := or              (at level 85, right associativity) : boolean_scope.
Notation "p ⇒ q"  := (¬ p ∨ q)       (at level 86, right associativity) : boolean_scope.
Notation "⊤"      := true            (at level 0, no associativity) : boolean_scope.
Notation "⊥"      := false           (at level 0, no associativity) : boolean_scope.
Infix    "∧"      := and             (at level 80, right associativity) : boolean_scope.
Infix    "⟹"     := implies         (at level 99, right associativity) : boolean_scope.
Infix    "≈"      := equivalent      (at level 90, no associativity) : boolean_scope.

Declare Scope ltl_scope.
Bind Scope ltl_scope with Formula.
Delimit Scope ltl_scope with ltl.
Open Scope boolean_scope.
Open Scope ltl_scope.

Notation "◯ p"       := (next p)             (at level 75, right associativity) : ltl_scope.
Notation "◇ p"       := (eventually p)       (at level 75, right associativity) : ltl_scope.
Notation "□ p"       := (always p)           (at level 75, right associativity) : ltl_scope.
Notation "p 'U' q"   := (until p q)          (at level 79, right associativity) : ltl_scope.
Notation "p 'W' q"   := (wait p q)           (at level 79, right associativity) : ltl_scope.
Notation "p 'R' q"   := (release p q)        (at level 79, right associativity) : ltl_scope.
Notation "p 'M' q"   := (strong_release p q) (at level 79, right associativity) : ltl_scope.
Notation "'Λ' x , p" := (examine (λ x , p))  (at level 97, no associativity) : ltl_scope.

Program Instance implies_reflexive : Reflexive implies := impl_reflexive.
Program Instance implies_transitive : Transitive implies := impl_transitive.
Program Instance Equivalence_equivalent : Equivalence equivalent := Equivalence_equiv.

Program Instance equivalent_respects_equivalent :
  Proper (equivalent ==> equivalent ==> iff) equivalent := equiv_respects_equiv.

Program Instance not_respects_implies : Proper (implies --> implies) not | 1 :=
  negate_respects_impl.

Ltac induct :=
  try split; repeat intro; simpl in *;
  match goal with
    [ S : list S.a |- _ ] => induction S
  end; firstorder.

#[local] Obligation Tactic := induct.

Program Instance Examine_respects_implies :
  Proper ((eq ==> implies) ==> implies) Examine.
Program Instance Examine_respects_equivalent :
  Proper ((eq ==> equivalent) ==> equivalent) Examine.

Instance and_respects_implies :
  Proper (implies ==> implies ==> implies) and := And_respects_impl.
Instance or_respects_implies :
  Proper (implies ==> implies ==> implies) or := Or_respects_impl.
Instance next_respects_implies :
  Proper (implies ==> implies) next := Next_respects_impl.
Instance until_respects_implies :
  Proper (implies ==> implies ==> implies) until := Until_respects_impl.
Instance wait_respects_implies :
  Proper (implies ==> implies ==> implies) wait := Wait_respects_impl.
Instance eventually_respects_implies :
  Proper (implies ==> implies) eventually := Eventually_respects_impl.
Instance always_respects_implies :
  Proper (implies ==> implies) always := Always_respects_impl.
Instance release_respects_implies :
  Proper (implies ==> implies ==> implies) release := Release_respects_impl.
Instance strong_release_respects_implies :
  Proper (implies ==> implies ==> implies) strong_release :=
  StrongRelease_respects_impl.

Lemma implication p q : SL.implies (denote p) (denote q) -> (p ⟹ q).
Proof.
  repeat intro.
  apply denote_matches.
  apply denote_matches in H0.
  now apply H.
Qed.

Theorem or_inj p q : p ⟹ p ∨ q.
Proof. now induct. Qed.

Theorem true_def p : p ∨ ¬p ≈ ⊤.
Proof.
  split; repeat intro;
  simpl; intuition.
  clear H.
  rewrite matches_negate.
  exact (classic (matches p s)).
Qed.

Theorem false_def p : ¬(p ∨ ¬p) ≈ ⊥.
Proof.
  split; repeat intro;
  simpl; intuition.
  rewrite matches_negate in H.
  apply H.
  rewrite true_def.
  now constructor.
Qed.

Theorem or_comm p q : p ∨ q ≈ q ∨ p.
Proof. now induct. Qed.

Theorem or_assoc p q r : (p ∨ q) ∨ r ≈ p ∨ (q ∨ r).
Proof. now induct. Qed.

Theorem and_def p q : p ∧ q ≈ ¬(¬p ∨ ¬q).
Proof. now induct; rewrite !negate_negate in *. Qed.

Theorem huntington p q : ¬(¬p ∨ ¬q) ∨ ¬(¬p ∨ q) ≈ p.
Proof.
  unfold or, not; simpl.
  rewrite !negate_negate.
  split; repeat intro; simpl in *; intuition.
  pose proof (true_def q).
  destruct H0.
  clear H0.
  specialize (H1 s I).
  simpl in H1.
  now intuition.
Qed.

Theorem (* 1 *) next_not p : ◯ ¬p ≈ ¬◯ p.
Proof. now auto. Qed.

Theorem (* 2 *) next_impl p q : ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Proof. now induct. Qed.

Theorem (* 10 *) until_expand p q : p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Proof. now induct. Qed.

Theorem (* 9 *) next_until p q : ◯ (p U q) ≈ (◯ p) U (◯ q).
Proof. now split; apply implication, next_until. Qed.

Theorem (* 11 *) until_false p : p U ⊥ ≈ ⊥.
Proof. now induct. Qed.

Theorem (* NEW *) looped p : ◯ ¬p U p ⟹ p.
Proof. now induct; contradiction (matches_not_false H1 H). Qed.

Theorem (* 12 *) until_left_or p q r : p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Proof. now induct. Qed.

Theorem (* 14 *) until_left_and p q r : p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Proof. now induct. Qed.

Theorem (* NEW *) until_and_until p q r s :
  (p U q) ∧ (r U s) ⟹ (p ∧ r) U ((q ∧ r) ∨ (p ∧ s) ∨ (q ∧ s)).
Proof. now induct. Qed.

Theorem (* 17 *) until_left_or_order p q r : p U (q U r) ⟹ (p ∨ q) U r.
Proof. now induct; right; induct. Qed.

Theorem (* 18 *) until_right_and_order p q r : p U (q ∧ r) ⟹ (p U q) U r.
Proof. now apply implication, until_right_and_order. Qed.

Theorem (* 170 *) not_until p q : ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).
Proof. now induct. Qed.

Theorem (* 38 *) evn_def p : ◇ p ≈ ⊤ U p.
Proof. now induct. Qed.

Theorem (* 54 *) always_def p : □ p ≈ ¬◇ ¬p.
Proof. now induct; rewrite ?negate_negate in *; intuition. Qed.

Theorem (* 169 *) wait_def p q : p W q ≈ □ p ∨ p U q.
Proof. now induct. Qed.

Theorem release_def p q : p R q ≈ ¬(¬p U ¬q).
Proof. now induct; rewrite ?negate_negate in *; intuition. Qed.

Theorem strong_release_def p q : p M q ≈ q U (p ∧ q).
Proof. now induct. Qed.

Section Combinators.

Definition if_then (p : S.a -> bool) (f : S.a -> Formula) :=
  Λ x, match x with
       | Some x => if p x then f x else ⊤
       | None => ⊤
       end.

Fixpoint series (l : list Formula) : Formula :=
  match l with
  | nil => ⊤
  | x :: nil => x
  | x :: xs => x ∧ Next (series xs)
  end.

End Combinators.

End LTL.

Require Import Coq.Arith.PeanoNat.

Module NatStream <: StreamType.

Definition a := nat.

End NatStream.

Module LTLExamples.

Module Import L := LTL NatStream.

Definition num (n : nat) :=
  Λ x, match x with
       | Some x => if x =? n then ⊤ else ⊥
       | None => ⊥
       end.

Example ex_match_query  :
  matches (num 1 ∧ ◯ (num 2)) [1; 2].
Proof. now simpl. Qed.

Example ex_match_series :
  matches (series [num 1; num 2]) [1; 2].
Proof. now simpl. Qed.

Example ex_match_sample1 :
  matches (◇ (num 3 ⇒ ◇ (num 8))) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. now simpl; intuition. Qed.

Example ex_match_sample2 :
  matches (◇ (if_then (λ n, n =? 3) (λ n, ◇ (num (n + 5)))))
          [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. now simpl; intuition. Qed.

End LTLExamples.
