Require Import
  Program
  Coq.Lists.List
  Coq.Classes.Equivalence
  Coq.omega.Omega
  Coq.Sets.Ensembles
  Hask.Control.Monad
  Hask.Data.Monoid
  Hask.Data.Maybe.

Require Import Equations.Equations.
Require Import Equations.EqDec.

Open Scope program_scope.
Open Scope list_scope.

Require Import LTL.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Section Match.

Variable a : Type.              (* The type of entries in the trace *)
Variable term : Type.

Inductive Match : Type :=
  | EndOfTrace     (l : LTL a) (t : term)
  | IsTrue
  | Base           (x : a)
  | Negated
  | Both           (p q : Match)
  | InLeft         (p : Match)
  | InRight        (q : Match)
  | NextFwd        (p : Match)
  | EventuallyStop (p : Match)
  | EventuallyFwd  (p : Match)
  | UntilPrf1      (p : Match) (ps : Match)
  | UntilPrf2      (q : Match)
  | AlwaysPrf1     (p : Match) (ps : Match)
  | AlwaysPrf2.

Open Scope ltl_scope.

Fixpoint compare (t : Maybe term) (l : LTL a) (s : Stream a) :=
  match l return Maybe Match with
  | ⊤       => Just IsTrue
  | ⊥       => Nothing

  | Query v => match s with
               | []     => EndOfTrace (Query v) <$> t
               | x :: _ => compare t (v x) s
               end

  | ¬ p     => match compare t p s with
               | Nothing   => Just Negated
               | Just _ => Nothing
               end

  | p ∧ q   => Both    <$> compare t p s <*> compare t q s
  | p ∨ q   => InLeft  <$> compare t p s
           <|> InRight <$> compare t q s

  | X p     => match s with
               | []      => EndOfTrace (X p) <$> t
               | _ :: xs => NextFwd <$> compare t p xs
               end

  | p U q   => let fix go s :=
                   match s with
                   | []      => EndOfTrace (p U q) <$> t
                   | x :: xs => UntilPrf2 <$> compare t q (x :: xs)
                            <|> UntilPrf1 <$> compare t p (x :: xs)
                                          <*> go xs
                   end in go s

  | ◇ p     => let fix go s :=
                   match s with
                   | []      => EndOfTrace (◇ p) <$> t
                   | x :: xs => EventuallyStop <$> compare t p (x :: xs)
                            <|> EventuallyFwd  <$> go xs
                   end in go s

  | □ p     => let fix go s :=
                   match s with
                   | []      => Just AlwaysPrf2
                   | x :: xs => AlwaysPrf1 <$> compare t p (x :: xs)
                                           <*> go xs
                   end in go s
  end.

Lemma compare_correct (L : LTL a) (T : Stream a) :
  forall t,
    (exists P, compare t L T = Just P)
      <-> matches a (match t with Nothing => False | _ => True end) L T.
Proof.
  intros.
  generalize dependent T;
  induction L;
  intros; auto.
  - now simpl; firstorder eauto.
  - simpl; firstorder eauto; discriminate.
  - destruct T, t; simpl in *;
    firstorder eauto.
    discriminate.
  - specialize (IHL T);
    simpl; firstorder eauto;
    destruct (compare t L T) eqn:?.
    + discriminate.
    + intuition; firstorder eauto; discriminate.
    + contradiction H1.
      eapply H; eauto.
    + now eexists; eauto.
  - specialize (IHL1 T);
    specialize (IHL2 T);
    simpl;
    destruct (compare t L1 T) eqn:?;
    destruct (compare t L2 T) eqn:?;
    destruct t; simpl in *;
    firstorder eauto.
  - specialize (IHL1 T);
    specialize (IHL2 T);
    simpl;
    destruct (compare t L1 T) eqn:?;
    destruct (compare t L2 T) eqn:?;
    destruct t; simpl in *;
    firstorder eauto.
  - split; intros.
    + destruct H, T; simpl in *; auto.
        destruct t; auto; discriminate.
      apply IHL; clear IHL.
      apply fmap_endo_just in H.
      now firstorder eauto.
    + destruct T, t; simpl in *; auto;
      [ eexists; eauto | contradiction | .. ];
      apply IHL in H;
      destruct H;
      exists (NextFwd x);
      apply fmap_endo_just;
      exists x; auto.
  - split; intros;
    induction T; simpl in *; auto.
    + destruct H, t; auto; discriminate.
    + destruct H.
      apply alt_endo_just in H.
      destruct H; intuition auto.
      * apply fmap_endo_just in H.
        destruct H, H; subst.
        left.
        apply IHL2.
        now firstorder eauto.
      * apply fmap_endo_nothing in H0.
        apply ap_endo_just in H1.
        destruct H1, H, H, H1; subst.
        rewrite H2 in IHT; clear H2.
        right.
        split.
          apply IHL1.
          now firstorder eauto.
        apply IHT.
        now eexists; eauto.
    + destruct t; auto; simpl.
        now eexists; eauto.
      contradiction.
    + destruct H.
        apply IHL2 in H.
        destruct H.
        rewrite H; simpl.
        now eexists; eauto.
      destruct H.
      apply IHL1 in H.
      destruct H.
      rewrite H; simpl.
      intuition auto.
      destruct H1.
      rewrite H1; clear H1.
      destruct (compare t L2 (a0 :: T)) eqn:?; simpl;
      now eexists; eauto.
  - split; intros;
    induction T; simpl in *; auto.
    + destruct t; auto.
      destruct H; discriminate.
    + destruct H.
      apply alt_endo_just in H.
      destruct H.
      * apply fmap_endo_just in H.
        destruct H, H; subst.
        now firstorder eauto.
      * destruct H.
        apply fmap_endo_just in H0.
        destruct H0, H0; subst.
        now firstorder eauto.
    + destruct t; auto; simpl.
        now eexists; eauto.
      contradiction.
    + destruct H.
        apply IHL in H.
        destruct H.
        eexists.
        apply alt_endo_just.
        left.
        apply fmap_endo_just.
        now firstorder eauto.
      intuition.
      destruct H0.
      rewrite H0; clear H0.
      destruct (compare t L (a0 :: T)) eqn:?.
        eexists.
        apply alt_endo_just.
        now left; simpl; auto.
      eexists.
      apply alt_endo_just.
      now right; split; auto.
  - split; intros;
    induction T; simpl in *; auto.
    + destruct H.
      apply ap_endo_just in H.
      destruct H, H, H, H0.
      now firstorder eauto.
    + now eexists; eauto.
    + destruct H.
      intuition.
      destruct H1.
      apply IHL in H.
      destruct H.
      eexists.
      apply ap_endo_just.
      do 2 eexists.
      now firstorder eauto.
Qed.

(*
Inductive MatchDep : LTL -> Type :=
  | DepEndOfTrace     (t : term) (l : LTL)                       : MatchDep l
  | DepIsTrue                                                    : MatchDep Top
  | DepBase           q (w : b)                                  : MatchDep (Query q)
  | DepBoth           `(P : MatchDep p) `(Q : MatchDep q)        : MatchDep (p ∧ q)
  | DepInLeft         `(P : MatchDep p) q                        : MatchDep (p ∨ q)
  | DepInRight        p `(Q : MatchDep q)                        : MatchDep (p ∨ q)
  | DepImplied1       p q                                        : MatchDep (p → q)
  | DepImplied2       `(P : MatchDep p) `(Q : MatchDep q)        : MatchDep (p → q)
  | DepNextFwd        `(P : MatchDep p)                          : MatchDep (X p)
  | DepEventuallyStop `(P : MatchDep p)                          : MatchDep (◇ p)
  | DepEventuallyFwd  `(P : MatchDep p)                          : MatchDep (◇ p)
  | DepUntilPrf1      `(P : MatchDep p) `(PS : MatchDep (p U q)) : MatchDep (p U q)
  | DepUntilPrf2      p `(Q : MatchDep q)                        : MatchDep (p U q)
  | DepAlwaysPrf1     `(P : MatchDep p) `(PS : MatchDep (□ p))   : MatchDep (□ p)
  | DepAlwaysPrf2     p                                          : MatchDep (□ p).
*)

Variable t : Maybe term.

Notation "T ⊢ L ⟿ P" := (compare t L T = Just P) (at level 80).

Definition Match_equiv (p q : Match) : Prop := p = q.

Ltac end_of_trace := apply EndOfTrace; [auto|intro; discriminate].

Lemma match_neg P T φ : (T ⊢ ¬φ ⟿ P) <-> ~ (T ⊢ φ ⟿ P).
Proof.
Abort.

End Match.

Arguments EndOfTrace {a term} _ _.
Arguments IsTrue {a term}.
Arguments Base {a term} x.
Arguments Negated {a term}.
Arguments Both {a term} p q.
Arguments InLeft {a term} p.
Arguments InRight {a term} q.
Arguments NextFwd {a term} p.
Arguments EventuallyStop {a term} p.
Arguments EventuallyFwd {a term} p.
Arguments UntilPrf1 {a term} p ps.
Arguments UntilPrf2 {a term} q.
Arguments AlwaysPrf1 {a term} p ps.
Arguments AlwaysPrf2 {a term}.

Section Examples.

Open Scope ltl_scope.

Example ex_compare_sample :
  compare nat () Nothing (□ (ifThen (fun n => n =? 3)
                                 (fun n => X (◇ (num (n + 5))))))
          [1; 2; 3; 4; 5; 6; 7; 8; 9]
    = Just
        (AlwaysPrf1 IsTrue
           (AlwaysPrf1 IsTrue
              (AlwaysPrf1
                 (NextFwd
                    (EventuallyFwd
                       (EventuallyFwd
                          (EventuallyFwd
                             (EventuallyFwd
                                (EventuallyStop IsTrue))))))
                 (AlwaysPrf1 IsTrue
                    (AlwaysPrf1 IsTrue
                       (AlwaysPrf1 IsTrue
                          (AlwaysPrf1 IsTrue
                             (AlwaysPrf1 IsTrue
                                (AlwaysPrf1 IsTrue
                                   (AlwaysPrf2)))))))))).
Proof. reflexivity. Qed.

End Examples.

CoInductive Pipe (m : Type -> Type) (i o : Type) : Type :=
  | HaveOutput (x : o) (p : Pipe m i o)
  | NeedInput (k : i -> Pipe m i o)
  | Effect t (e : m t) (k : t -> Pipe m i o)
  | Done (x : o).

Arguments HaveOutput {m i o} _ _.
Arguments NeedInput {m i o} _.
Arguments Effect {m i o} _ _.
Arguments Done {m i o} _.

CoInductive pipe_eq {m i o} (m_eq : forall t, m t -> m t -> Prop) :
  Pipe m i o -> Pipe m i o -> Prop :=
  | HaveOutput_eq : forall f g x y,
      x = y -> pipe_eq m_eq f g ->
      pipe_eq m_eq (HaveOutput x f) (HaveOutput y g)
  | NeedInput_eq : forall f g,
      (forall x, pipe_eq m_eq (f x) (g x)) ->
      pipe_eq m_eq (NeedInput f) (NeedInput g)
  | Effect_eq : forall t f g u v,
      m_eq t u v ->
      (forall x, pipe_eq m_eq (f x) (g x)) ->
      pipe_eq m_eq (Effect t u f) (Effect t v g)
  | Done_eq : forall x y,
      x = y -> pipe_eq m_eq (Done x) (Done y).

Definition frob `(f : Pipe m i o) : Pipe m i o :=
  match f with
  | HaveOutput x f => HaveOutput x f
  | NeedInput k    => NeedInput k
  | Effect t e k   => Effect t e k
  | Done x         => Done x
  end.

Theorem frob_eq : forall `(f : Pipe m i o), f = frob f.
Proof. destruct f; reflexivity. Qed.

Inductive Result (a b : Type) := Success (s : b) | Failure (f : a).

Arguments Success {_ _} _.
Arguments Failure {_ _} _.

Program Instance Semigroup_Result `{Semigroup a} `{Semigroup b} :
  Semigroup (Result a b) := {
  mappend := fun x y =>
    match x, y with
    | Failure x, Failure y => Failure (x ⨂ y)
    | Success _, Failure y => Failure y
    | Failure x, Success _ => Failure x
    | Success x, Success y => Success (x ⨂ y)
    end
}.
Next Obligation.
  destruct a0, b0, c; simpl; auto.
  now rewrite mappend_assoc.
Qed.

Program Instance Semigroup_unit : Semigroup () := {
  mappend := fun _ _ => ()
}.

Definition Engine (m : Type -> Type) (a : Type) :=
  Pipe m a (Result () (Match a ())).

CoFixpoint combine `{Monad m} {i o} (f g : Pipe m i o) : Pipe m i o :=
  match f with
  | HaveOutput x p => HaveOutput x (combine p g)
  | NeedInput k    => NeedInput (fun a => combine (k a) g)
  | Effect t e k   => Effect t e (fun a => combine (k a) g)
  | Done x         => HaveOutput x g
  end.

Lemma pipe_eq_refl `{Monad m} {i o} :
  forall (f : Pipe m i o) (m_eq : forall t, m t -> m t -> Prop),
  (forall t e, m_eq t e e) -> pipe_eq m_eq f f.
Proof.
  cofix Heq.
  intros.
  rewrite (frob_eq f).
  destruct f;
  simpl; constructor; auto.
Qed.

Lemma combine_assoc `{Monad m} {i o} :
  forall (f g h : Pipe m i o) (m_eq : forall t, m t -> m t -> Prop),
  (forall t e, m_eq t e e) ->
  pipe_eq m_eq (combine f (combine g h)) (combine (combine f g) h).
Proof.
  cofix Heq.
  intros.
  rewrite (frob_eq (combine f (combine g h))).
  rewrite (frob_eq (combine (combine f g) h)).
  simpl.
  destruct f; simpl; constructor; auto.
  now apply pipe_eq_refl.
Qed.

Program Instance Semigroup_Pipe `{Monad m} {i o} : Semigroup (Pipe m i o) := {
  mappend := combine
}.

Open Scope ltl_scope.

Fixpoint toPipe `{Monad m} {i} (l : LTL i) {struct l} : Engine m i :=
  match l with
  | ⊤       => let cofix go := HaveOutput (Success IsTrue) go in go
  | ⊥       => let cofix go := HaveOutput (Failure ()) go in go
  | Query v => NeedInput (toPipe ∘ v)
  | ¬ p     => Done (Failure ()) (* map over outputs, flipping success/failure *)
  | p ∧ q   => combine (toPipe p) (toPipe q)
  | p ∨ q   => Done (Failure ())
  | X p     => Done (Failure ())
  | p U q   => Done (Failure ())
  | ◇ p     => Done (Failure ())
  | □ p     => Done (Failure ())
  end.
