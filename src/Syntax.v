Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.Lists.List
  Coq.Classes.Morphisms
  Coq.Logic.Classical
  FunInd
  Stream
  Bool
  LTL.

Open Scope program_scope.
Open Scope list_scope.

Import ListNotations.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Module Type StreamType.

Parameter a : Type.              (* The type of entries in the trace *)

End StreamType.

Module LTL (S : StreamType) <: LinearTemporalLogicW <: LinearTemporalLogic.

(** This data type encodes the syntax of LTL in Positive Normal Form (PNF). *)
Inductive Formula : Type :=
  (* Boolean layer *)
  | Top
  | Bottom

  | Examine (v : option S.a -> Formula)

  | And   (p q : Formula)
  | Or    (p q : Formula)

  (* Temporal layer *)
  | Next       (p : Formula)

  | Until      (p q : Formula)
  | Release    (p q : Formula)

  | Always     (p : Formula)
  | Eventually (p : Formula)

  | Wait          (p q : Formula)
  | StrongRelease (p q : Formula).

Definition t := Formula.

Fixpoint size (p : t) : nat :=
  match p with
  | Top               => 1
  | Bottom            => 1
  | Examine v         => 1
  | And p q           => 1 + size p + size q
  | Or p q            => 1 + size p + size q
  | Next p            => 1 + size p
  | Until p q         => 1 + size p + size q
  | Release p q       => 1 + size p + size q
  | Always p          => 1 + size p
  | Eventually p      => 1 + size p
  | Wait p q          => 1 + size p + size q
  | StrongRelease p q => 1 + size p + size q
  end.

Function negate (l : t) : t :=
  match l with
  | Top               => Bottom
  | Bottom            => Top
  | Examine v         => Examine (negate ∘ v)
  | And p q           => Or (negate p) (negate q)
  | Or p q            => And (negate p) (negate q)
  | Next p            => Next (negate p)
  | Until p q         => Release (negate p) (negate q)
  | Release p q       => Until (negate p) (negate q)
  | Always p          => Eventually (negate p)
  | Eventually p      => Always (negate p)
  | Wait p q          => StrongRelease (negate p) (negate q)
  | StrongRelease p q => Wait (negate p) (negate q)
  end.

Fixpoint expand (l : t) : t :=
  match l with
  | Top               => l
  | Bottom            => l

  | Examine v         => Examine (expand ∘ v)

  | And p q           => And (expand p) (expand q)
  | Or p q            => Or (expand p) (expand q)

  | Next p            => Next (expand p)

  | Until p q         => Or (expand q) (And (expand p) (Next (Until p q)))
  | Release p q       => And (expand q) (Or (expand p) (Next (Release p q)))

  (* jww (2021-02-18): NYI *)
  | Always p          => And (expand p) (Next (Always p))
  | Eventually p      => Or (expand p) (Next (Eventually p))

  | Wait p q          => Or (expand q) (And (expand p) (Next (Wait p q)))
  | StrongRelease p q => And (expand q) (Or (expand p) (Next (StrongRelease p q)))
  end.

Definition basic (l : t) : Prop :=
  match l with
  | Until p q         => False
  | Release p q       => False
  | Always p          => False
  | Eventually p      => False
  | Wait p q          => False
  | StrongRelease p q => False
  | _                 => True
  end.

Lemma basic_expand : forall l, basic (expand l).
Proof. induction l; simpl; auto. Qed.

Fixpoint shallow (l : t) : Prop :=
  match l with
  | Top               => True
  | Bottom            => True
  | Examine v         => True
  | And p q           => shallow p /\ shallow q
  | Or p q            => shallow p /\ shallow q
  | Next p            => True
  | Until p q         => False
  | Always p          => False
  | Eventually p      => False
  | Release p q       => False
  | Wait p q          => False
  | StrongRelease p q => False
  end.

Lemma expand_complete (l : t) : shallow (expand l).
Proof. induction l; simpl in *; intuition auto. Qed.

(** Prune out any instances of Top or Bottom *)
Function prune (l : t) : t :=
  match l with
  | Top       => l
  | Bottom    => l
  | Examine v => l

  | And p q =>
    match prune p with
    | Top => prune q
    | _   =>
      match prune q with
      | Top => prune p
      | _   => And (prune p) (prune q)
      end
    end

  | Or p q =>
    match prune p with
    | Bottom => prune q
    | _      =>
      match prune q with
      | Bottom => prune p
      | _      => Or (prune p) (prune q)
      end
    end

  | Next p            => Next (prune p)
  | Until p q         => Until (prune p) (prune q)
  | Release p q       => Release (prune p) (prune q)
  | Always p          => Always (prune p)
  | Eventually p      => Eventually (prune p)
  | Wait p q          => Wait (prune p) (prune q)
  | StrongRelease p q => StrongRelease (prune p) (prune q)
  end.

Inductive Matches : t -> Stream S.a -> Prop :=
  | MatchTop s :
      Matches Top s
  | MatchBottom s :
      Matches Bottom s
  | MatchExamine v x xs :
      Matches (v (Some x)) (Cons x xs) -> Matches (Examine v) (Cons x xs)
  | MatchAnd p q s :
      Matches p s -> Matches q s -> Matches (And p q) s
  | MatchOr p q s :
      Matches p s \/ Matches q s -> Matches (Or p q) s
  | MatchNext p x xs :
      Matches p xs -> Matches (Next p) (Cons x xs)
  | MatchUntil p q x xs :
      Matches q (Cons x xs)
        \/ (Matches p (Cons x xs) /\ Matches (Until p q) xs) ->
      Matches (Until p q) (Cons x xs)
  | MatchAlways p x xs :
      Matches p (Cons x xs) -> Matches (Always p) xs ->
      Matches (Always p) (Cons x xs)
  | MatchEventually p x xs :
      Matches p (Cons x xs) \/ Matches (Eventually p) xs ->
      Matches (Eventually p) (Cons x xs)
  | MatchRelease p q x xs :
      Matches q (Cons x xs)
        -> (Matches p (Cons x xs) \/ Matches (Release p q) xs) ->
      Matches (Release p q) (Cons x xs)
  | MatchWait p q x xs :
      Matches q (Cons x xs)
        \/ (Matches p (Cons x xs) /\ Matches (Wait p q) xs) ->
      Matches (Wait p q) (Cons x xs)
  | MatchStrongRelease p q x xs :
      Matches q (Cons x xs)
        \/ (Matches p (Cons x xs) /\ Matches (StrongRelease p q) xs) ->
      Matches (StrongRelease p q) (Cons x xs).

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

  | Release p q =>
    let fix go s :=
        match s with
        | nil     => matches q s
        | _ :: xs => matches q s /\ (matches p s \/ go xs)
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

  | Wait p q =>
    let fix go s :=
        match s with
        | nil     => matches q s \/ matches p s
        | _ :: xs => matches q s \/ (matches p s /\ go xs)
        end in go s

  | StrongRelease p q =>
    let fix go s :=
        match s with
        | nil     => matches q s /\ matches p s
        | _ :: xs => matches q s /\ (matches p s \/ go xs)
        end in go s
  end.

Definition true           := Top.
Definition false          := Bottom.
Definition and            := And.
Definition or             := Or.
Definition not            := negate.
Definition implies        := fun p q => forall s, matches p s -> matches q s.
Definition equivalent     := fun p q => implies p q /\ implies q p.
Definition next           := Next.
Definition until          := Until.
Definition release        := Release.
Definition always         := Always.
Definition eventually     := Eventually.
Definition wait           := Wait.
Definition strong_release := StrongRelease.
Definition examine        := Examine.

Declare Scope boolean_scope.
Bind Scope boolean_scope with t.
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
Bind Scope ltl_scope with t.
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

Ltac inv H := inversion H; subst; clear H.

Program Instance Examine_respects_implies :
  Proper ((eq ==> implies) ==> implies) Examine.
Next Obligation.
  repeat intro; simpl in *.
  destruct s; intuition;
  now apply (H _ _ (reflexivity _)).
  (* inv H0. *)
  (* constructor. *)
  (* specialize (H a a (reflexivity _)). *)
  (* now apply H. *)
Qed.

Program Instance Examine_respects_equivalent :
  Proper ((eq ==> equivalent) ==> equivalent) Examine.
Next Obligation.
  split; repeat intro.
  - destruct s; intuition;
    now apply (H _ _ (reflexivity _)).
  - destruct s; intuition;
    now apply (H _ _ (reflexivity _)).
Qed.

Program Instance matches_respects_implies :
  Proper (implies ==> eq ==> Basics.impl) matches.
Next Obligation.
  repeat intro.
  subst.
  now apply H.
Qed.

Program Instance matches_respects_equivalent :
  Proper (equivalent ==> eq ==> iff) (matches).
Next Obligation.
  split; repeat intro.
  - subst.
    now apply H.
  - subst.
    now apply H.
Qed.

Program Instance And_respects_implies : Proper (implies ==> implies ==> implies) And.
Next Obligation.
  repeat intro.
  simpl.
  now rewrite <- H, <- H0.
Qed.

Program Instance And_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) And.
Next Obligation.
  split; repeat intro.
  - destruct H, H0.
    now rewrite <- H, <- H0.
  - destruct H, H0.
    now rewrite <- H2, <- H3.
Qed.

Program Instance Or_respects_implies : Proper (implies ==> implies ==> implies) Or.
Next Obligation.
  repeat intro.
  simpl.
  now rewrite <- H, <- H0.
Qed.

Program Instance Or_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) Or.
Next Obligation.
  split; repeat intro.
  - destruct H, H0.
    now rewrite <- H, <- H0.
  - destruct H, H0.
    now rewrite <- H2, <- H3.
Qed.

Program Instance Next_respects_implies : Proper (implies ==> implies) Next.
Next Obligation.
  repeat intro.
  simpl in *;
  destruct s; now auto.
Qed.

Program Instance Next_respects_equivalent : Proper (equivalent ==> equivalent) Next.
Next Obligation.
  split; repeat intro.
  - simpl in *;
    destruct s; auto;
    now rewrite <- H.
  - simpl in *;
    destruct s; auto;
    now rewrite H.
Qed.

Program Instance Until_respects_implies : Proper (implies ==> implies ==> implies) Until.
Next Obligation.
  repeat intro.
  now induction s; simpl in *; intuition.
Qed.

Program Instance Until_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) Until.
Next Obligation.
  split; destruct H, H0;
  now apply Until_respects_implies.
Qed.

Program Instance Release_respects_implies : Proper (implies ==> implies ==> implies) Release.
Next Obligation.
  repeat intro.
  now induction s; simpl in *; intuition.
Qed.

Program Instance Release_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) Release.
Next Obligation.
  split; destruct H, H0;
  now apply Release_respects_implies.
Qed.

Program Instance Always_respects_implies : Proper (implies ==> implies) Always.
Next Obligation.
  repeat intro.
  now induction s; simpl in *; intuition.
Qed.

Program Instance Always_respects_equivalent : Proper (equivalent ==> equivalent) Always.
Next Obligation.
  split; destruct H;
  now apply Always_respects_implies.
Qed.

Program Instance Eventually_respects_implies : Proper (implies ==> implies) Eventually.
Next Obligation.
  repeat intro.
  now induction s; simpl in *; intuition.
Qed.

Program Instance Eventually_respects_equivalent : Proper (equivalent ==> equivalent) Eventually.
Next Obligation.
  split; destruct H;
  now apply Eventually_respects_implies.
Qed.

Program Instance Wait_respects_implies : Proper (implies ==> implies ==> implies) Wait.
Next Obligation.
  repeat intro.
  now induction s; simpl in *; intuition.
Qed.

Program Instance Wait_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) Wait.
Next Obligation.
  split; destruct H, H0;
  now apply Wait_respects_implies.
Qed.

Program Instance StrongRelease_respects_implies : Proper (implies ==> implies ==> implies) StrongRelease.
Next Obligation.
  repeat intro.
  now induction s; simpl in *; intuition.
Qed.

Program Instance StrongRelease_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) StrongRelease.
Next Obligation.
  split; destruct H, H0;
  now apply StrongRelease_respects_implies.
Qed.

Lemma expand_until (φ ψ : Formula) : φ U ψ ≈ ψ ∨ (φ ∧ ◯ (φ U ψ)).
Proof.
  split; simpl; intros s H;
  simpl in H;
  destruct s; simpl;
  now intuition.
Qed.

Lemma expand_release (φ ψ : Formula) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).
Proof.
  split; simpl; intros s H;
  simpl in H;
  destruct s; simpl;
  now intuition.
Qed.

Lemma expand_always (φ : Formula) : □ φ ≈ φ ∧ ◯ □ φ.
Proof.
  split; simpl; intros s H;
  simpl in H;
  destruct s; simpl;
  now intuition.
Qed.

Lemma expand_eventually (φ : Formula) : ◇ φ ≈ φ ∨ ◯ ◇ φ.
Proof.
  split; simpl; intros s H;
  simpl in H;
  destruct s; simpl;
  now intuition.
Qed.

Lemma expand_wait (φ ψ : Formula) : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).
Proof.
  split; simpl; intros s H;
  simpl in H;
  destruct s; simpl;
  now intuition.
Qed.

Lemma expand_strong_release (φ ψ : Formula) : φ M ψ ≈ ψ ∧ (φ ∨ ◯ (φ M ψ)).
Proof.
  split; simpl; intros s H;
  simpl in H;
  destruct s; simpl;
  now intuition.
Qed.

Lemma expand_correct l : expand l ≈ l.
Proof.
  induction l; simpl; intuition;
  rewrite ?IHl, ?IHl1, ?IHl2; simpl in *; intuition.
  - unfold Basics.compose.
    apply Examine_respects_equivalent.
    repeat intro; subst.
    now rewrite H.
  - now rewrite <- expand_until.
  - now rewrite <- expand_release.
  - now rewrite <- expand_always.
  - now rewrite <- expand_eventually.
  - now rewrite <- expand_wait.
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
      apply not_and_or in H.
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
        now simpl in *; intuition.
      simpl matches in H.
      apply not_or_and in H.
      destruct H;
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

Lemma matches_not_false {p s} : matches p s -> matches (¬ p) s -> False.
Proof.
  intros.
  rewrite matches_negate in H0.
  contradiction.
Qed.

Program Instance negate_respects_implies : Proper (implies --> implies) negate | 1.
Next Obligation.
  repeat intro.
  unfold flip in H.
  apply matches_negate.
  apply matches_negate in H0.
  intro.
  apply H in H1.
  contradiction.
Qed.

Program Instance not_respects_implies : Proper (implies --> implies) not | 1.
Next Obligation.
  unfold not.
  repeat intro.
  now rewrite <- H.
Qed.

Instance and_respects_implies :
  Proper (implies ==> implies ==> implies) and := And_respects_implies.
Instance or_respects_implies :
  Proper (implies ==> implies ==> implies) or := Or_respects_implies.
Instance next_respects_implies :
  Proper (implies ==> implies) next := Next_respects_implies.
Instance until_respects_implies :
  Proper (implies ==> implies ==> implies) until := Until_respects_implies.
Instance eventually_respects_implies :
  Proper (implies ==> implies) eventually := Eventually_respects_implies.
Instance always_respects_implies :
  Proper (implies ==> implies) always := Always_respects_implies.
Instance wait_respects_implies :
  Proper (implies ==> implies ==> implies) wait := Wait_respects_implies.
Instance release_respects_implies :
  Proper (implies ==> implies ==> implies) release := Release_respects_implies.
Instance strong_release_respects_implies :
  Proper (implies ==> implies ==> implies) strong_release := StrongRelease_respects_implies.

Theorem or_inj (p q : t) : p ⟹ p ∨ q.
Proof.
  repeat intro.
  simpl; intuition.
Qed.

Theorem true_def (p : t) : p ∨ ¬p ≈ ⊤.
Proof.
  split; repeat intro;
  simpl; intuition.
  clear H.
  rewrite matches_negate.
  exact (classic (matches p s)).
Qed.

Theorem false_def (p : t) : ¬(p ∨ ¬p) ≈ ⊥.
Proof.
  split; repeat intro;
  simpl; intuition.
  rewrite matches_negate in H.
  apply H.
  rewrite true_def.
  constructor.
Qed.

Theorem or_comm (p q : t) : p ∨ q ≈ q ∨ p.
Proof.
  split; repeat intro;
  simpl in *; intuition.
Qed.

Theorem or_assoc (p q r : t) : (p ∨ q) ∨ r ≈ p ∨ (q ∨ r).
Proof.
  split; repeat intro;
  simpl in *; intuition.
Qed.

Theorem and_def (p q : t) : p ∧ q ≈ ¬(¬p ∨ ¬q).
Proof.
  unfold and, or, not.
  simpl.
  now rewrite !negate_negate.
Qed.

Theorem huntington (p q : t) : ¬(¬p ∨ ¬q) ∨ ¬(¬p ∨ q) ≈ p.
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

Theorem next_not (p : t) : ◯ ¬p ≈ ¬◯ p.
Proof. now auto. Qed.

Theorem next_impl (p q : t) : ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Proof.
  unfold next, not, or.
  split; repeat intro; simpl in *;
  induction s; simpl in *; intuition.
Qed.

Theorem until_expansion (p q : t) : p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Proof.
  unfold until, or.
  split; repeat intro; simpl in *;
  now induction s; intuition.
Qed.

Theorem next_until (p q : t) : ◯ (p U q) ≈ (◯ p) U (◯ q).
Proof.
  unfold next, until.
  split; repeat intro;
  induction s; intuition;
  rewrite until_expansion; simpl;
  rewrite until_expansion in H; simpl in H;
  now intuition.
Qed.

Theorem until_right_bottom (p : t) : p U ⊥ ≈ ⊥.
Proof.
  unfold until, false.
  split; repeat intro; simpl in *;
  now induction s; intuition.
Qed.

Theorem until_left_or (p q r : t) : p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Proof.
  unfold until, or.
  split; repeat intro; simpl in *;
  now induction s; intuition.
Qed.

Theorem until_right_or (p q r : t) : (p U r) ∨ (q U r) ⟹ (p ∨ q) U r.
Proof.
  unfold until, or.
  repeat intro; simpl in *;
  now induction s; intuition.
Qed.

Theorem until_left_and (p q r : t) : p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Proof.
  unfold until, or.
  repeat intro; simpl in *;
  now induction s; intuition.
Qed.

Theorem until_right_and (p q r : t) : (p ∧ q) U r ≈ (p U r) ∧ (q U r).
Proof.
  unfold until, or.
  split; repeat intro; simpl in *;
  now induction s; intuition.
Qed.

Theorem until_impl_order (p q r : t) : (p U q) ∧ (¬q U r) ⟹ p U r.
Proof.
  unfold until, and, not.
  repeat intro; simpl in *;
  induction s; intuition.
  contradiction (matches_not_false H H1).
Qed.

Theorem until_right_or_order (p q r : t) : p U (q U r) ⟹ (p ∨ q) U r.
Proof.
  unfold until, and, not.
  repeat intro; simpl in *;
  induction s; intuition.
  right.
  split; auto.
  apply IHs.
  now destruct s; simpl; intuition.
Qed.

Lemma matches_top s : matches Top s <-> True.
Proof. reflexivity. Qed.

Lemma matches_bottom s : matches Bottom s <-> False.
Proof. reflexivity. Qed.

Lemma matches_examine_nil v :
  matches (Examine v) nil <-> matches (v None) nil.
Proof. reflexivity. Qed.

Lemma matches_examine_cons x xs v :
  matches (Examine v) (x :: xs) <-> matches (v (Some x)) (x :: xs).
Proof. reflexivity. Qed.

Lemma matches_and s p q : matches (And p q) s <-> matches p s /\ matches q s.
Proof. reflexivity. Qed.

Lemma matches_or s p q : matches (Or p q) s <-> matches p s \/ matches q s.
Proof. reflexivity. Qed.

Lemma matches_next x xs p : matches (Next p) (x :: xs) <-> matches p xs.
Proof. reflexivity. Qed.

Lemma matches_until x xs p q :
  matches (Until p q) (x :: xs) <->
  matches q (x :: xs) \/ (matches p (x :: xs) /\ matches (Until p q) xs).
Proof. reflexivity. Qed.

Lemma matches_release x xs p q :
  matches (Release p q) (x :: xs) <->
  matches q (x :: xs) /\ (matches p (x :: xs) \/ matches (Release p q) xs).
Proof. reflexivity. Qed.

Lemma matches_always x xs p :
  matches (Always p) (x :: xs) <->
  matches p (x :: xs) /\ matches (Always p) xs.
Proof. reflexivity. Qed.

Lemma matches_eventually x xs p :
  matches (Eventually p) (x :: xs) <->
  matches p (x :: xs) \/ matches (Eventually p) xs.
Proof. reflexivity. Qed.

Lemma matches_wait s p q : matches (Wait p q) s <-> True.
Proof.
Abort.

Lemma matches_strongrelease s p q : matches (StrongRelease p q) s <-> True.
Proof.
Abort.

Theorem until_right_and_order (p q r : t) : p U (q ∧ r) ⟹ (p U q) U r.
Proof.
  unfold until, and.
  repeat intro;
  induction s; intuition.
  - now simpl in *; intuition.
  - rewrite matches_until, matches_and in *.
    destruct H.
      now intuition.
    destruct H.
    specialize (IHs H0).
    destruct (classic (matches r (a :: s))); auto.
    right; split; auto.
    destruct (classic (matches q (a :: s))); auto.
      now left.
    rewrite matches_until in *.
    right; split; auto.
    clear -H0.
    now induction s; simpl in *; intuition.
Qed.

Theorem not_until (p q : t) : ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).
Proof.
  unfold until, or.
  split; repeat intro; simpl in *;
  now induction s; intuition.
Qed.

Theorem evn_def (p : t) : ◇ p ≈ ⊤ U p.
Proof.
  unfold eventually, until.
  split; repeat intro; simpl in *;
  now induction s; intuition.
Qed.

Theorem always_def (p : t) : □ p ≈ ¬◇ ¬p.
Proof.
  unfold eventually, until.
  split; repeat intro; simpl in *;
  induction s; intuition.
  - now rewrite negate_negate.
  - now rewrite negate_negate.
  - now rewrite negate_negate in H.
  - now rewrite negate_negate in H0.
Qed.

Theorem always_induction_ (p : t) : □ (p ⇒ ◯ p) ⟹ p ⇒ □ p.
Proof.
  unfold eventually, until.
  repeat intro; simpl in *;
  induction s; firstorder.
  - contradiction (matches_not_false H H1).
  - destruct (true_def p).
    specialize (H2 (a :: s)).
    specialize (H3 (a :: s)).
    now firstorder.
Qed.

Theorem always_until_and_ind (p q r : t) :
  □ (p ⇒ (◯ p ∧ q) ∨ r) ⟹ p ⇒ □ q ∨ q U r.
Proof.
  unfold eventually, until.
  repeat intro; simpl in *;
  induction s; intuition.
  contradiction (matches_not_false H H3).
Qed.

Theorem always_and_until (p q r : t) : □ p ∧ q U r ⟹ (p ∧ q) U (p ∧ r).
Proof.
  unfold always, until, and.
  repeat intro; simpl in *;
  now induction s; intuition.
Qed.

Theorem wait_def (p q : t) : p W q ≈ □ p ∨ p U q.
Proof.
  unfold wait, until.
  split; repeat intro; simpl in *;
  now induction s; intuition.
Qed.

Theorem release_def (p q : t) : p R q ≈ ¬(¬p U ¬q).
Proof.
  unfold release, until.
  split; repeat intro; simpl in *;
  induction s; intuition;
  rewrite ?negate_negate in *; intuition.
Qed.

Theorem strong_release_def (p q : t) : p M q ≈ q U (p ∧ q).
Proof.
  unfold strong_release, until, and.
  split; repeat intro; simpl in *;
  now induction s; intuition.
Qed.

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
  matches (num 1 ∧ ◯ (num 2)) [1; 2].
Proof. simpl; auto. Qed.

Example ex_match_series :
  matches (series [num 1; num 2]) [1; 2].
Proof. simpl; auto. Qed.

Example ex_match_sample1 :
  matches (◇ (num 3 ⇒ ◇ (num 8))) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. simpl; intuition auto. Qed.

Example ex_match_sample2 :
  matches (◇ (if_then (λ n, n =? 3) (λ n, ◇ (num (n + 5)))))
          [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. simpl; intuition auto. Qed.

End LTLExamples.
