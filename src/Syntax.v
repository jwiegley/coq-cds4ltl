Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.Lists.List
  Coq.Classes.Morphisms
  Coq.Logic.Classical
  FunInd
  Model
  Stream
  Bool
  LTL.

Open Scope program_scope.
Open Scope list_scope.

Import ListNotations.

Module LTL (S : StreamType) <: LinearTemporalLogicW <: LinearTemporalLogic.

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

Definition t := Formula.

(*
Fixpoint denote (l : Formula) : L.t :=
  match l with
  | Top               => true
  | Bottom            => false
  | Examine v         => fun s => denote (v (head s)) s
  | And p q           => denote p ∧ denote q
  | Or p q            => denote p ∨ denote q
  | Next p            => ◯ (denote p)
  | Until p q         => (denote p) U (denote q)
  | Wait p q          => (denote p) W (denote q)
  | Always p          => □ (denote p)
  | Eventually p      => ◇ (denote p)
  | Release p q       => (denote p) R (denote q)
  | StrongRelease p q => (denote p) M (denote q)
  end.
*)

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

Fixpoint expand (l : Formula) : Formula :=
  match l with
  | Top               => l
  | Bottom            => l
  | Examine v         => Examine (expand ∘ v)
  | And p q           => And (expand p) (expand q)
  | Or p q            => Or (expand p) (expand q)
  | Next p            => Next (expand p)
  | Until p q         => Or (expand q) (And (expand p) (Next (Until p q)))
  | Wait p q          => Or (expand q) (And (expand p) (Next (Wait p q)))
  | Always p          => And (expand p) (Next (Always p))
  | Eventually p      => Or (expand p) (Next (Eventually p))
  | Release p q       => And (expand q) (Or (expand p) (Next (Release p q)))
  | StrongRelease p q => And (expand q) (Or (expand p) (Next (StrongRelease p q)))
  end.

Definition basic (l : Formula) : Prop :=
  match l with
  | Until p q         => False
  | Wait p q          => False
  | Always p          => False
  | Eventually p      => False
  | Release p q       => False
  | StrongRelease p q => False
  | _                 => True
  end.

Lemma basic_expand : forall l, basic (expand l).
Proof. induction l; simpl; auto. Qed.

Fixpoint shallow (l : Formula) : Prop :=
  match l with
  | Top               => True
  | Bottom            => True
  | Examine v         => True
  | And p q           => shallow p /\ shallow q
  | Or p q            => shallow p /\ shallow q
  | Next p            => True
  | Until p q         => False
  | Wait p q          => False
  | Always p          => False
  | Eventually p      => False
  | Release p q       => False
  | StrongRelease p q => False
  end.

Lemma expand_complete (l : Formula) : shallow (expand l).
Proof. induction l; simpl in *; intuition auto. Qed.

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

Fixpoint matches (l : Formula) (s : list S.a) : option (Matches l s) :=
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
      match matches (v None) nil with
      | Some r => Some (MatchExamineEnd v r)
      | None   => None
      end
    | x :: xs => fun Heqe : s = x :: xs =>
      match matches (v (Some x)) s with
      | Some r => Some (MatchExamine v x xs (rew Heqe in r))
      | None   => None
      end
    end eq_refl

  | And p q =>
    match matches p s with
    | Some r =>
      match matches q s with
      | Some t => Some (MatchAnd p q s r t)
      | None   => None
      end
    | None   => None
    end

  | Or p q  =>
    match matches p s with
    | Some r => Some (MatchOrLeft p q s r)
    | None   =>
      match matches q s with
      | Some t => Some (MatchOrRight p q s t)
      | None   => None
      end
    end

  | Next p =>
    match s with
    | nil => None
    | x :: xs =>
      match matches p xs with
      | Some r => Some (MatchNext p x xs r)
      | None   => None
      end
    end

  | Until p q =>
    let fix go s : option (Matches (Until p q) s) :=
        match matches q s with
        | Some r  => Some (MatchUntilStop p q s r)
        | None =>
          match s as s' return s = s' -> _ with
          | nil => fun _ => None
          | x :: xs => fun Heqe : s = x :: xs =>
            match matches p s with
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
            match matches q s with
            | Some r  => Some (rew Heqe in MatchWaitStop p q s r)
            | None =>
              match matches p s with
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
            match matches p s with
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
          match matches p s with
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
            match matches q s with
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
                  match matches p s with
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
          match matches q s with
          | Some r  =>
            match matches p s with
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

Fixpoint denote (l : Formula) (s : list S.a) {struct l} : Prop :=
  match l with
  | Top    => True
  | Bottom => False

  | Examine v =>
    match s with
    | nil    => denote (v None) s
    | x :: _ => denote (v (Some x)) s
    end

  | And p q => denote p s /\ denote q s
  | Or p q  => denote p s \/ denote q s

  | Next p =>
    match s with
    | nil     => denote p nil
    | x :: xs => denote p xs
    end

  | Until p q =>
    let fix go s :=
        match s with
        | nil     => denote q s
        | _ :: xs => denote q s \/ (denote p s /\ go xs)
        end in go s

  | Wait p q =>
    let fix go s :=
        match s with
        | nil     => denote q s \/ denote p s
        | _ :: xs => denote q s \/ (denote p s /\ go xs)
        end in go s

  | Always p =>
    let fix go s :=
        match s with
        | nil     => denote p s
        | _ :: xs => denote p s /\ go xs
        end in go s

  | Eventually p =>
    let fix go s :=
        match s with
        | nil     => denote p s
        | _ :: xs => denote p s \/ go xs
        end in go s

  | Release p q =>
    let fix go s :=
        match s with
        | nil     => denote q s
        | _ :: xs => denote q s /\ (denote p s \/ go xs)
        end in go s

  | StrongRelease p q =>
    let fix go s :=
        match s with
        | nil     => denote q s /\ denote p s
        | _ :: xs => denote q s /\ (denote p s \/ go xs)
        end in go s
  end.

Ltac inv H := inversion H; subst; clear H.

Theorem matches_denote l s x : matches l s = Some x -> denote l s.
Proof.
  intros.
  generalize dependent s.
  induction l; simpl; intros.
  + destruct s; inv H.
    now constructor.
  + now inv H.
  + destruct s; inv H0.
    * destruct (matches (v None) []) eqn:Heqe; inv H2.
      now intuition eauto.
    * destruct (matches (v (Some a)) (a :: s)) eqn:Heqe; inv H2.
      now intuition eauto.
  + destruct (matches l1 s) eqn:Heqe1; inv H.
    destruct (matches l2 s) eqn:Heqe2; inv H1.
    now split; intuition eauto.
  + destruct (matches l1 s) eqn:Heqe1; inv H.
    * now left; intuition eauto.
    * destruct (matches l2 s) eqn:Heqe2; inv H1.
      now right; intuition eauto.
  + destruct s; inv H.
    destruct (matches l s) eqn:Heqe; inv H1.
    now intuition eauto.
  + induction s.
    * destruct (matches l2 []) eqn:Heqe2; inv H.
      now intuition eauto.
    * destruct (matches l2 (a :: s)) eqn:Heqe2; inv H.
      ** now left; intuition eauto.
      ** destruct (matches l1 (a :: s)) eqn:Heqe1; inv H1.
         destruct (_ s); inv H0.
         right; intuition eauto.
         now eapply IHs; eauto.
  + induction s.
    * destruct (matches l2 []) eqn:Heqe2; inv H.
    * destruct (matches l2 (a :: s)) eqn:Heqe2; inv H.
      ** now left; intuition eauto.
      ** destruct (matches l1 (a :: s)) eqn:Heqe1; inv H1.
         destruct (_ s); inv H0.
         *** right; intuition eauto.
             now eapply IHs; eauto.
         *** right.
             split.
             **** now intuition eauto.
             **** now destruct s; inv H1.
  + induction s.
    * now inv H.
    * destruct (matches l (a :: s)) eqn:Heqe; inv H.
      split.
      ** now intuition eauto.
      ** destruct (_ s).
         *** now eapply IHs; eauto.
         *** destruct s.
             **** now inv H1.
             **** now inv H1.
  + induction s.
    * now inv H.
    * destruct (matches l (a :: s)) eqn:Heqe; inv H.
      ** now left; intuition eauto.
      ** right.
         destruct (_ s).
         *** now eapply IHs; eauto.
         *** now inv H1.
  + induction s.
    * now inv H.
    * destruct (matches l2 (a :: s)) eqn:Heqe2; inv H.
      destruct (matches l1 (a :: s)) eqn:Heqe1; inv H1.
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
    * destruct (matches l2 (a :: s)) eqn:Heqe2; inv H.
      destruct (matches l1 (a :: s)) eqn:Heqe1; inv H1.
      ** now intuition eauto.
      ** destruct (_ s); inv H0.
         intuition eauto.
         right; intuition eauto.
         now eapply IHs; eauto.
Qed.

Definition true           := Top.
Definition false          := Bottom.
Definition and            := And.
Definition or             := Or.
Definition not            := negate.
Definition implies        := fun p q => forall s, denote p s -> denote q s.
Definition equivalent     := fun p q => implies p q /\ implies q p.
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
Notation "'Λ' f , g" := (examine (λ f , g))  (at level 97, no associativity) : ltl_scope.

Program Instance implies_reflexive : Reflexive implies.
Next Obligation. now repeat intro. Qed.

Program Instance implies_transitive : Transitive implies.
Next Obligation.
  repeat intro.
  now apply H0, H.
Qed.

Program Instance Equivalence_equivalent : Equivalence equivalent.
Next Obligation. split; repeat intro; auto. Qed.
Next Obligation. split; repeat intro; firstorder. Qed.
Next Obligation. split; repeat intro; firstorder. Qed.

Program Instance equivalent_respects_equivalent :
  Proper (equivalent ==> equivalent ==> iff) equivalent.
Next Obligation.
  split; repeat intro.
  - now rewrite <- H0, <- H1, <- H.
  - now rewrite H0, <- H1.
Qed.

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

Program Instance matches_respects_implies :
  Proper (implies ==> eq ==> Basics.impl) denote.
Next Obligation.
  - subst; now apply H.
  - subst; now apply H.
Qed.

Program Instance matches_respects_equivalent :
  Proper (equivalent ==> eq ==> iff) denote.
Next Obligation.
  - subst; now apply H.
  - subst; now apply H.
  - subst; now apply H2.
  - subst; now apply H2.
Qed.

Program Instance And_respects_implies :
  Proper (implies ==> implies ==> implies) And.

Program Instance And_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) And.

Program Instance Or_respects_implies :
  Proper (implies ==> implies ==> implies) Or.

Program Instance Or_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) Or.

Program Instance Next_respects_implies :
  Proper (implies ==> implies) Next.

Program Instance Next_respects_equivalent :
  Proper (equivalent ==> equivalent) Next.

Program Instance Until_respects_implies :
  Proper (implies ==> implies ==> implies) Until.

Program Instance Until_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) Until.

Program Instance Wait_respects_implies :
  Proper (implies ==> implies ==> implies) Wait.

Program Instance Wait_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) Wait.

Program Instance Always_respects_implies :
  Proper (implies ==> implies) Always.

Program Instance Always_respects_equivalent :
  Proper (equivalent ==> equivalent) Always.

Program Instance Eventually_respects_implies :
  Proper (implies ==> implies) Eventually.

Program Instance Eventually_respects_equivalent :
  Proper (equivalent ==> equivalent) Eventually.

Program Instance Release_respects_implies :
  Proper (implies ==> implies ==> implies) Release.

Program Instance Release_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) Release.

Program Instance StrongRelease_respects_implies :
  Proper (implies ==> implies ==> implies) StrongRelease.

Program Instance StrongRelease_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) StrongRelease.

Lemma expand_until (φ ψ : Formula) : φ U ψ ≈ ψ ∨ (φ ∧ ◯ (φ U ψ)).
Proof. now induct. Qed.

Lemma expand_release (φ ψ : Formula) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).
Proof. now induct. Qed.

Lemma expand_always (φ : Formula) : □ φ ≈ φ ∧ ◯ □ φ.
Proof. now induct. Qed.

Lemma expand_eventually (φ : Formula) : ◇ φ ≈ φ ∨ ◯ ◇ φ.
Proof. now induct. Qed.

Lemma expand_wait (φ ψ : Formula) : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).
Proof. now induct. Qed.

Lemma expand_strong_release (φ ψ : Formula) : φ M ψ ≈ ψ ∧ (φ ∨ ◯ (φ M ψ)).
Proof. now induct. Qed.

Lemma expand_correct l : expand l ≈ l.
Proof.
  induction l; simpl; intuition;
  rewrite ?IHl, ?IHl1, ?IHl2; simpl in *; intuition.
  - unfold Basics.compose.
    apply Examine_respects_equivalent.
    repeat intro; subst.
    now rewrite H.
  - now rewrite <- expand_until.
  - now rewrite <- expand_wait.
  - now rewrite <- expand_always.
  - now rewrite <- expand_eventually.
  - now rewrite <- expand_release.
  - now rewrite <- expand_strong_release.
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

Lemma denote_negate x s : denote (negate x) s <-> ~ denote x s.
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
      simpl denote in H.
      apply not_or_and in H.
      destruct H.
      apply not_and_or in H0.
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        now simpl in *; intuition.
      simpl denote in H.
      apply not_or_and in H.
      destruct H.
      apply not_and_or in H0.
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        now simpl in *; intuition.
      simpl denote in H.
      apply not_and_or in H.
      destruct H;
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        now simpl in *; intuition.
      simpl denote in H.
      apply not_or_and in H.
      destruct H;
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        now simpl in *; intuition.
      simpl denote in H.
      apply not_and_or in H.
      destruct H;
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        simpl denote in H.
        apply not_and_or in H.
        now simpl in *; intuition.
      simpl denote in H.
      apply not_and_or in H.
      destruct H.
        now simpl in *; intuition.
      apply not_or_and in H.
      now simpl in *; intuition.
Qed.

Lemma negate_negate p : negate (negate p) ≈ p.
Proof.
  split; repeat intro;
  rewrite !denote_negate in *.
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

Lemma denote_not_false {p s} : denote p s -> denote (¬ p) s -> False.
Proof.
  intros.
  rewrite denote_negate in H0.
  contradiction.
Qed.

Program Instance negate_respects_implies : Proper (implies --> implies) negate | 1.
Next Obligation.
  - apply denote_negate.
    apply denote_negate in H0.
    now firstorder.
  - apply denote_negate.
    apply denote_negate in H0.
    now firstorder.
Qed.

Program Instance not_respects_implies : Proper (implies --> implies) not | 1.
Next Obligation.
  - unfold not in *.
    apply denote_negate.
    apply denote_negate in H0.
    now firstorder.
  - unfold not in *.
    apply denote_negate.
    apply denote_negate in H0.
    now firstorder.
Qed.

Instance and_respects_implies :
  Proper (implies ==> implies ==> implies) and := And_respects_implies.
Instance or_respects_implies :
  Proper (implies ==> implies ==> implies) or := Or_respects_implies.
Instance next_respects_implies :
  Proper (implies ==> implies) next := Next_respects_implies.
Instance until_respects_implies :
  Proper (implies ==> implies ==> implies) until := Until_respects_implies.
Instance wait_respects_implies :
  Proper (implies ==> implies ==> implies) wait := Wait_respects_implies.
Instance eventually_respects_implies :
  Proper (implies ==> implies) eventually := Eventually_respects_implies.
Instance always_respects_implies :
  Proper (implies ==> implies) always := Always_respects_implies.
Instance release_respects_implies :
  Proper (implies ==> implies ==> implies) release := Release_respects_implies.
Instance strong_release_respects_implies :
  Proper (implies ==> implies ==> implies) strong_release :=
  StrongRelease_respects_implies.

Theorem or_inj p q : p ⟹ p ∨ q.
Proof. now induct. Qed.

Theorem true_def p : p ∨ ¬p ≈ ⊤.
Proof.
  split; repeat intro;
  simpl; intuition.
  clear H.
  rewrite denote_negate.
  exact (classic (denote p s)).
Qed.

Theorem false_def p : ¬(p ∨ ¬p) ≈ ⊥.
Proof.
  split; repeat intro;
  simpl; intuition.
  rewrite denote_negate in H.
  apply H.
  rewrite true_def.
  constructor.
Qed.

Theorem or_comm p q : p ∨ q ≈ q ∨ p.
Proof. now induct. Qed.

Theorem or_assoc p q r : (p ∨ q) ∨ r ≈ p ∨ (q ∨ r).
Proof. now induct. Qed.

Theorem and_def p q : p ∧ q ≈ ¬(¬p ∨ ¬q).
Proof.
  unfold and, or, not.
  simpl.
  now rewrite !negate_negate.
Qed.

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
  intuition.
Qed.

Theorem (* 1 *) next_not p : ◯ ¬p ≈ ¬◯ p.
Proof. now auto. Qed.

Theorem (* 2 *) next_impl p q : ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Proof. now induct. Qed.

Theorem (* 10 *) until_expand p q : p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Proof. now induct. Qed.

Theorem (* 9 *) next_until p q : ◯ (p U q) ≈ (◯ p) U (◯ q).
Proof.
  unfold next, until.
  split; repeat intro;
  induction s; intuition;
  rewrite until_expand; simpl;
  rewrite until_expand in H; simpl in H;
  now intuition.
Qed.

Theorem (* 11 *) until_false p : p U ⊥ ≈ ⊥.
Proof. now induct. Qed.

Theorem (* NEW *) looped p : ◯ ¬p U p ⟹ p.
Proof.
  induct.
  contradiction (denote_not_false H1 H).
Qed.

Theorem (* NEW *) until_and_not_ p q : p U q ∧ ¬q ⟹ (p ∧ ¬q) U (p ∧ ¬q ∧ ◯ q).
Proof.
  unfold until.
  repeat intro; simpl in *.
  induction s; intuition.
  - contradiction (denote_not_false H0 H1).
  - contradiction (denote_not_false H H1).
  - destruct (classic (denote q s)).
    + now firstorder.
    + apply denote_negate in H.
      now firstorder.
Qed.

Theorem (* 12 *) until_left_or p q r : p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Proof. now induct. Qed.

Theorem (* 14 *) until_left_and p q r : p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Proof. now induct. Qed.

Theorem (* NEW *) until_and_until p q r s :
  (p U q) ∧ (r U s) ⟹ (p ∧ r) U ((q ∧ r) ∨ (p ∧ s) ∨ (q ∧ s)).
Proof. now induct. Qed.

Theorem (* 17 *) until_left_or_order p q r : p U (q U r) ⟹ (p ∨ q) U r.
Proof.
  induct.
  right.
  now induct.
Qed.

Lemma denote_top s : denote Top s <-> True.
Proof. reflexivity. Qed.

Lemma denote_bottom s : denote Bottom s <-> False.
Proof. reflexivity. Qed.

Lemma denote_examine_nil v :
  denote (Examine v) nil <-> denote (v None) nil.
Proof. reflexivity. Qed.

Lemma denote_examine_cons x xs v :
  denote (Examine v) (x :: xs) <-> denote (v (Some x)) (x :: xs).
Proof. reflexivity. Qed.

Lemma denote_and s p q : denote (And p q) s <-> denote p s /\ denote q s.
Proof. reflexivity. Qed.

Lemma denote_or s p q : denote (Or p q) s <-> denote p s \/ denote q s.
Proof. reflexivity. Qed.

Lemma denote_next x xs p : denote (Next p) (x :: xs) <-> denote p xs.
Proof. reflexivity. Qed.

Lemma denote_until x xs p q :
  denote (Until p q) (x :: xs) <->
  denote q (x :: xs) \/ (denote p (x :: xs) /\ denote (Until p q) xs).
Proof. reflexivity. Qed.

Lemma denote_wait x xs p q :
  denote (Wait p q) (x :: xs) <->
  denote q (x :: xs) \/ (denote p (x :: xs) /\ denote (Wait p q) xs).
Proof. reflexivity. Qed.

Lemma denote_always x xs p :
  denote (Always p) (x :: xs) <->
  denote p (x :: xs) /\ denote (Always p) xs.
Proof. reflexivity. Qed.

Lemma denote_eventually x xs p :
  denote (Eventually p) (x :: xs) <->
  denote p (x :: xs) \/ denote (Eventually p) xs.
Proof. reflexivity. Qed.

Lemma denote_release x xs p q :
  denote (Release p q) (x :: xs) <->
  denote q (x :: xs) /\ (denote p (x :: xs) \/ denote (Release p q) xs).
Proof. reflexivity. Qed.

Lemma denote_strongrelease x xs p q :
  denote (StrongRelease p q) (x :: xs) <->
  denote q (x :: xs) /\ (denote p (x :: xs) \/ denote (StrongRelease p q) xs).
Proof. reflexivity. Qed.

Theorem (* 18 *) until_right_and_order p q r : p U (q ∧ r) ⟹ (p U q) U r.
Proof.
  unfold until, and.
  repeat intro;
  induction s; intuition.
  - now simpl in *; intuition.
  - rewrite denote_until, denote_and in *.
    firstorder.
    destruct (classic (denote r (a :: s))); auto.
    right; split; auto.
    destruct (classic (denote q (a :: s))); auto.
      now left.
    rewrite denote_until in *.
    right; split; auto.
    clear -H0.
    now induct.
Qed.

Theorem (* 170 *) not_until p q : ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).
Proof. now induct. Qed.

Theorem (* 38 *) evn_def p : ◇ p ≈ ⊤ U p.
Proof. now induct. Qed.

Theorem (* 54 *) always_def p : □ p ≈ ¬◇ ¬p.
Proof. induct; rewrite ?negate_negate in *; intuition. Qed.

Theorem (* 169 *) wait_def p q : p W q ≈ □ p ∨ p U q.
Proof. now induct. Qed.

Theorem release_def p q : p R q ≈ ¬(¬p U ¬q).
Proof. induct; rewrite ?negate_negate in *; intuition. Qed.

Theorem strong_release_def p q : p M q ≈ q U (p ∧ q).
Proof. now induct. Qed.

End LTL.

Module LTLCombinators (S : StreamType).

Module Import L := LTL S.

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

End LTLCombinators.

Require Import Coq.Arith.PeanoNat.

Module NatStream <: StreamType.

Definition a := nat.

End NatStream.

Module LTLExamples.

Module Import C := LTLCombinators NatStream.
Import C.L.

Definition num (n : nat) :=
  Λ x, match x with
       | Some x => if x =? n then ⊤ else ⊥
       | None => ⊥
       end.

Example ex_match_query  :
  denote (num 1 ∧ ◯ (num 2)) [1; 2].
Proof. simpl; auto. Qed.

Example ex_match_series :
  denote (series [num 1; num 2]) [1; 2].
Proof. simpl; auto. Qed.

Example ex_match_sample1 :
  denote (◇ (num 3 ⇒ ◇ (num 8))) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. simpl; intuition auto. Qed.

Example ex_match_sample2 :
  denote (◇ (if_then (λ n, n =? 3) (λ n, ◇ (num (n + 5)))))
          [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. simpl; intuition auto. Qed.

End LTLExamples.
