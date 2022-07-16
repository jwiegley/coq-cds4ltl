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
  LTL
  Denote.

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

#[global]
Program Instance impl_Reflexive : Reflexive impl.
#[global]
Program Instance impl_Transitive : Transitive impl.
#[global]
Program Instance equiv_Equivalence : Equivalence equiv.

#[local] Obligation Tactic := program_simpl.

#[global]
Program Instance equiv_respects_equiv :
  Proper (equiv ==> equiv ==> iff) equiv.
Next Obligation.
  split; repeat intro.
  - now rewrite <- H0, <- H1, <- H.
  - now rewrite H0, <- H1.
Qed.

#[global]
Program Instance matches_respects_impl :
  Proper (impl ==> eq ==> Basics.impl) matches.
Next Obligation.
  repeat intro.
  subst; now apply H.
Qed.

#[global]
Program Instance matches_respects_equiv :
  Proper (equiv ==> eq ==> iff) matches.
Next Obligation.
  split; repeat intro.
  - subst; now apply H.
  - subst; now apply H.
Qed.

#[local] Obligation Tactic := induct.

#[global]
Program Instance And_respects_impl :
  Proper (impl ==> impl ==> impl) And.

#[global]
Program Instance And_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) And.

#[global]
Program Instance Or_respects_impl :
  Proper (impl ==> impl ==> impl) Or.

#[global]
Program Instance Or_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) Or.

#[global]
Program Instance Next_respects_impl :
  Proper (impl ==> impl) Next.

#[global]
Program Instance Next_respects_equiv :
  Proper (equiv ==> equiv) Next.

#[global]
Program Instance Until_respects_impl :
  Proper (impl ==> impl ==> impl) Until.

#[global]
Program Instance Until_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) Until.

#[global]
Program Instance Wait_respects_impl :
  Proper (impl ==> impl ==> impl) Wait.

#[global]
Program Instance Wait_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) Wait.

#[global]
Program Instance Always_respects_impl :
  Proper (impl ==> impl) Always.

#[global]
Program Instance Always_respects_equiv :
  Proper (equiv ==> equiv) Always.

#[global]
Program Instance Eventually_respects_impl :
  Proper (impl ==> impl) Eventually.

#[global]
Program Instance Eventually_respects_equiv :
  Proper (equiv ==> equiv) Eventually.

#[global]
Program Instance Release_respects_impl :
  Proper (impl ==> impl ==> impl) Release.

#[global]
Program Instance Release_respects_equiv :
  Proper (equiv ==> equiv ==> equiv) Release.

#[global]
Program Instance StrongRelease_respects_impl :
  Proper (impl ==> impl ==> impl) StrongRelease.

#[global]
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

#[global]
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

Module LTL (S : StreamType).

Module        O   := OptionStreamType S.
Module Import SL  := StreamLTL O.
Module Import L   := LinearTemporalLogicFacts SL.
Module Import LW  := LinearTemporalLogicWFacts SL.
Module Import ML  := MinimalLinearTemporalLogicFacts SL.
Module Import BF  := ML.BF.
Module Import MBF := BF.MBF.
Module Import AST := LTLSyntax S.

Module Denoted <: Denotation SL.

Definition A := Formula.

(** Syntactic formulae denote directly into stream-based LTL formulae. *)
Fixpoint denote (l : Formula) : t :=
  match l with
  | Top               => ⊤
  | Bottom            => ⊥
  | Examine v         => λ s, denote (v (head s)) s
  | And p q           => denote p ∧ denote q
  | Or p q            => denote p ∨ denote q
  | Next p            => ◯ denote p
  | Until p q         => denote p U denote q
  | Wait p q          => denote p W denote q
  | Always p          => □ denote p
  | Eventually p      => ◇ denote p
  | Release p q       => denote p R denote q
  | StrongRelease p q => denote p M denote q
  end.

Definition Top           : A              := Top.
Definition Bottom        : A              := Bottom.
Definition And           : A -> A -> A    := And.
Definition Or            : A -> A -> A    := Or.
Definition Not           : A -> A         := negate.
Definition Implies       : A -> A -> Prop := impl.
Definition Equivalent    : A -> A -> Prop := equiv.
Definition Next          : A -> A         := Next.
Definition Until         : A -> A -> A    := Until.
Definition Wait          : A -> A -> A    := Wait.
Definition Always        : A -> A         := Always.
Definition Eventually    : A -> A         := Eventually.
Definition Release       : A -> A -> A    := Release.
Definition StrongRelease : A -> A -> A    := StrongRelease.

Notation "'Λ' x , p" := (Examine (λ x , p))  (at level 97, no associativity) : ltl_scope.

Fixpoint project {A : Type} (xs : list A) : Stream (option A) :=
  match xs with
  | nil       => constant None
  | cons x xs => Cons (Some x) (project xs)
  end.

(** Prove that a constructive match against a finite trace is isomorphic to
    denoting that same formula into a stream-based model where we project the
    finite trace into an infinite stream by lifting the basis set to a pointed
    set and continuing the "point" to eternity beyond the end of the trace. *)
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
        intuition; lia.
      * destruct H.
        ** apply IHl2 in H.
           exists 0.
           intuition; lia.
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
           intuition; lia.
        ** apply IHl1 in H.
           left.
           intro.
           now induction i.
      * destruct H.
        ** clear IHs.
           right.
           apply IHl2 in H.
           exists 0.
           intuition; lia.
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
           *** intros; lia.
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
        ** intros; lia.
      * destruct H.
        destruct H0.
        ** clear IHs.
           exists 0.
           apply IHl1 in H0.
           apply IHl2 in H.
           split.
           *** now split.
           *** intros; lia.
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
    + unfold release, wait in H.
      induction s.
      * inv H.
        ** apply IHl2.
           now apply (H0 0).
        ** inv H0.
           destruct H.
           inv H.
           apply IHl2.
           now induction x; intuition.
      * inv H.
        ** split.
           *** apply IHl2.
               now apply (H0 0).
           *** right.
               apply IHs.
               left.
               intro.
               now apply (H0 (S i)).
        ** inv H0.
           destruct H.
           inv H.
           split.
           *** apply IHl2.
               destruct x.
               **** exact H1.
               **** apply (H0 0); lia.
           *** destruct x.
               **** left.
                    apply IHl1.
                    exact H2.
               **** right.
                    apply IHs.
                    right.
                    exists x.
                    split; auto; intros.
                    ***** now split.
                    ***** apply (H0 (S i)).
                          lia.
    + unfold strong_release in H.
      induction s.
      * inv H.
        destruct H0.
        inv H.
        split.
        ** apply IHl2.
           now induction x; intuition.
        ** apply IHl1.
           now induction x; intuition.
      * inv H.
        destruct H0.
        inv H.
        split.
        ** apply IHl2.
           destruct x.
           *** exact H1.
           *** apply (H0 0); lia.
        ** destruct x.
           *** left.
               apply IHl1.
               exact H2.
           *** right.
               apply IHs.
               exists x.
               split.
               **** now split.
               **** intros.
                    apply (H0 (S i)); lia.
Qed.

(** Homomorphisms *)

Lemma denote_true : ⊤ ≈ denote Top.
Proof. reflexivity. Qed.

Lemma denote_false : ⊥ ≈ denote Bottom.
Proof. reflexivity. Qed.

Lemma denote_and p q : denote p ∧ denote q ≈ denote (And p q).
Proof. reflexivity. Qed.

Lemma denote_or p q : denote p ∨ denote q ≈ denote (Or p q).
Proof. reflexivity. Qed.

Lemma denote_not p : ¬ (denote p) ≈ denote (negate p).
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

Lemma denote_implies p q : (denote p ⟹ denote q) -> Implies p q.
Proof.
  repeat intro.
  now apply denote_matches, H, denote_matches.
Qed.

Lemma denote_next p : ◯ denote p ≈ denote (Next p).
Proof. reflexivity. Qed.

Lemma denote_until p q : denote p U denote q ≈ denote (Until p q).
Proof. reflexivity. Qed.

Lemma denote_wait p q : denote p W denote q ≈ denote (Wait p q).
Proof. reflexivity. Qed.

Lemma denote_always p : □ denote p ≈ denote (Always p).
Proof. reflexivity. Qed.

Lemma denote_eventually p : ◇ denote p ≈ denote (Eventually p).
Proof. reflexivity. Qed.

Lemma denote_release p q : denote p R denote q ≈ denote (Release p q).
Proof. reflexivity. Qed.

Lemma denote_strong_release p q : denote p M denote q ≈ denote (StrongRelease p q).
Proof. reflexivity. Qed.

#[global]
Program Instance Implies_Reflexive  : Reflexive Implies.
Next Obligation. now firstorder. Qed.

#[global]
Program Instance Implies_Transitive : Transitive Implies.
Next Obligation. now firstorder. Qed.

End Denoted.

Module Import D  := Denoted.
Module Import DF := DenotationFacts SL D.

Notation "'Λ' x , p" := (Examine (λ x , p))  (at level 97, no associativity) : ltl_scope.

Section Combinators.

Open Scope boolean_scope.
Open Scope ltl_scope.

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
Import L.AST.
Import L.DF.

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
