Require Import
  Program
  Coq.Lists.List
  Coq.Relations.Relation_Definitions
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.omega.Omega
  Coq.Sets.Ensembles
  Hask.Control.Monad
  Hask.Data.Monoid
  Hask.Data.Maybe
  Hask.Prelude.

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

Section Pipe.

Variable m : Type -> Type.
Variable i : Type.
Variable o : Type.
Context `{Equivalence o}.

CoInductive Pipe : Type :=
  | HaveOutput (x : o) (p : Pipe)
  | NeedInput (k : i -> Pipe)
  | Effect t (e : m t) (k : t -> Pipe)
  | Done.

Arguments HaveOutput _ _.
Arguments NeedInput _.
Arguments Effect _ _.
Arguments Done.

Definition frob `(f : Pipe) : Pipe :=
  match f with
  | HaveOutput x f => HaveOutput x f
  | NeedInput k    => NeedInput k
  | Effect t e k   => Effect t e k
  | Done           => Done
  end.

Theorem frob_eq : forall f : Pipe, f = frob f.
Proof. destruct f; reflexivity. Qed.

CoInductive pipe_equiv : Pipe -> Pipe -> Prop :=
  | HaveOutput_eq : forall f g x y,
      x ≈ y -> pipe_equiv f g ->
      pipe_equiv (HaveOutput x f) (HaveOutput y g)
  | NeedInput_eq : forall f g : i -> Pipe,
      (forall x, pipe_equiv (f x) (g x)) ->
      pipe_equiv (NeedInput f) (NeedInput g)
  | Effect_eq : forall t (u v : m t) (f g : t -> Pipe),
      (forall x, pipe_equiv (f x) (g x)) ->
      pipe_equiv (Effect t u f) (Effect t v g)
  | Done_eq : pipe_equiv Done Done.

Lemma pipe_equiv_refl : forall f : Pipe, pipe_equiv f f.
Proof.
  cofix Heq.
  intros.
  rewrite (frob_eq f).
  destruct f; simpl;
  constructor; auto;
  reflexivity.
Qed.

Ltac existence :=
  repeat match goal with
         | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
           apply inj_pair2 in H; subst
         end.

Lemma pipe_equiv_sym : forall f g : Pipe, pipe_equiv f g -> pipe_equiv g f.
Proof.
  cofix Heq.
  intros f g.
  rewrite (frob_eq f).
  rewrite (frob_eq g).
  destruct f, g; simpl; intros;
  inversion H0; subst; clear H0;
  try (constructor; auto; now symmetry).
  existence.
  constructor; auto.
Qed.

Lemma pipe_equiv_trans :
  forall f g h : Pipe, pipe_equiv f g -> pipe_equiv g h -> pipe_equiv f h.
Proof.
  cofix Heq.
  intros f g h.
  rewrite (frob_eq f).
  rewrite (frob_eq g).
  rewrite (frob_eq h).
  destruct f, g, h; simpl; intros;
  inversion H0; subst; clear H0;
  inversion H1; subst; clear H1.
  - constructor; [ now transitivity x0 | intuition ].
  - constructor; intros; now intuition.
  - constructor; existence.
    intros.
    now eapply Heq; eauto.
  - constructor; now transitivity x0.
Qed.

Global Program Instance pipe_equiv_Equivalence :
  Equivalence pipe_equiv.
Next Obligation. repeat intro; now apply pipe_equiv_refl. Qed.
Next Obligation. repeat intro; now apply pipe_equiv_sym. Qed.
Next Obligation. repeat intro; now eapply pipe_equiv_trans; eauto. Qed.

CoFixpoint feedInput (input : i) (p : Pipe) : Pipe :=
  match p with
  | HaveOutput x p => HaveOutput x (feedInput input p)
  | NeedInput k    => k input
  | Effect t e k   => Effect t e (feedInput input ∘ k)
  | Done           => Done
  end.

Global Program Instance feedInput_Proper :
  Proper (eq ==> pipe_equiv ==> pipe_equiv) feedInput.
Next Obligation.
  cofix Heq.
  repeat intro.
  rewrite (frob_eq (feedInput x x0)).
  rewrite (frob_eq (feedInput y y0)).
  simpl.
  destruct x0, y0; simpl in *; intros;
  try constructor;
  inversion H1; subst; clear H1;
  existence; auto.
  - apply Heq; auto.
  - specialize (H4 y).
    destruct (k y), (k0 y); auto.
  - constructor; intros.
    unfold Basics.compose.
    apply Heq; auto.
Qed.

CoFixpoint combine (f g : Pipe) : Pipe :=
  match f with
  | HaveOutput x p => HaveOutput x (combine p g)
  | NeedInput k    => NeedInput (fun a => combine (k a) (feedInput a g))
  | Effect t e k   => Effect t e (fun a => combine (k a) g)
  | Done           => g
  end.

Global Program Instance combine_Proper :
  Proper (pipe_equiv ==> pipe_equiv ==> pipe_equiv) combine.
Next Obligation.
  cofix Heq.
  repeat intro.
  rewrite (frob_eq (combine x x0)).
  rewrite (frob_eq (combine y y0)).
  simpl.
  destruct x, y, x0, y0; simpl in *; intros;
  try constructor;
  inversion H0; subst; clear H0;
  inversion H1; subst; clear H1;
  existence;
  repeat (try constructor; auto; try apply Heq; intros);
  apply feedInput_Proper;
  first [ reflexivity | now constructor ].
Qed.

Lemma feedInput_combine (input : i) (f g : Pipe) :
  pipe_equiv (feedInput input (combine f g))
             (combine (feedInput input f) (feedInput input g)).
Proof.
  revert input f g.
  cofix Heq.
  intros.
  rewrite (frob_eq (feedInput input (combine f g))).
  rewrite (frob_eq (combine (feedInput input f) (feedInput input g))).
  simpl.
  destruct f; simpl;
  try constructor;
  try reflexivity;
  intros; apply Heq.
Qed.

End Pipe.

Arguments combine {m i o} _ _.
Arguments frob_eq {m i o} _.
Arguments pipe_equiv {m i o _ _} _ _.

Lemma combine_assoc :
  forall {m i o} `{Ho : @Equivalence o Ro} {f g h : Pipe m i o},
    pipe_equiv (combine f (combine g h)) (combine (combine f g) h).
Proof.
  cofix Heq.
  intros.
  rewrite (frob_eq (combine f (combine g h))).
  rewrite (frob_eq (combine (combine f g) h)).
  simpl.
  destruct f; try constructor; intros;
  try reflexivity;
  fold (combine (m:=m) (i:=i) (o:=o)).
  - apply Heq.
  - rewrite feedInput_combine.
    admit.
  - apply Heq.
Admitted.

Instance Semigroup_Pipe {m i o} `{Equivalence o} : Semigroup (Pipe m i o) := {
  mappend          := combine;
  mappend_respects := combine_Proper _ _ _;
  mappend_assoc    := fun _ _ _ => combine_assoc
}.

CoFixpoint Pipe_map {m i} `{Equivalence a} `{Equivalence b}
           (f : a -> b) (x : Pipe m i a) : Pipe m i b :=
  match x with
  | HaveOutput x p => HaveOutput x (Pipe_map f p)
  | NeedInput k    => NeedInput (Pipe_map f ∘ k)
  | Effect t e k   => Effect t e (Pipe_map f ∘ k)
  | Done x         => Done (f x)
  end.

Fixpoint Pipe_bind `{Equivalence a} `{Equivalence b}
  (f : a -> Pipe b) (p : Pipe a) : Pipe b :=
  match p with
  | NeedInput  fa     => NeedInput (Pipe_bind f ∘ fa)
  | HaveOutput a  fa  => Pipe_bind (fun b => HaveOutput b (Pipe_bind f fa)) (f a)
  | Effect     _ t k  => Effect _ t (Pipe_bind f ∘ k)
  | Done       r      => f r
  end.

Inductive Result (a : Type) := Success (s : a) | Failure (f : a).

Arguments Success {_} _.
Arguments Failure {_} _.

Definition result_equiv `{Equivalence a} (x y : Result a) : Prop :=
  match x, y with
  | Success s1, Success s2 => s1 ≈ s2
  | Failure f1, Failure f2 => f1 ≈ f2
  | _, _ => False
  end.

Program Instance Result_Equivalence `{Equivalence a} :
  Equivalence result_equiv.
Next Obligation.
  repeat intro.
  destruct x; simpl; reflexivity.
Qed.
Next Obligation.
  repeat intro.
  destruct x, y; simpl in *;
  first [ now symmetry | contradiction ].
Qed.
Next Obligation.
  repeat intro.
  destruct x, y, z; simpl in *;
  first [ now rewrite H1 | contradiction ].
Qed.

Program Instance Semigroup_Result `{@Semigroup a RA HA} :
  @Semigroup (Result a) result_equiv Result_Equiv := {
  mappend := fun x y =>
    match x, y with
    | Failure x, Failure y => Failure (x ⨂ y)
    | Success _, Failure y => Failure y
    | Failure x, Success _ => Failure x
    | Success x, Success y => Success (x ⨂ y)
    end;
  mappend_respects := _
}.
Next Obligation.
  repeat intro.
  destruct x, y, x0, y0; simpl;
  simpl; auto;
  try contradiction;
  apply mappend_respects;
  first [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  destruct a0, b, c; simpl; try reflexivity;
  apply mappend_assoc.
Qed.

Definition Result_map `(f : a -> b) `(x : Result a) : Result b :=
  match x with
  | Success x => Success (f x)
  | Failure x => Failure (f x)
  end.

Definition Engine := Pipe (Result (Match i ())).

Instance Semigroup_Engine : Semigroup Engine := Semigroup_Pipe.

Open Scope ltl_scope.

Fixpoint toPipe (l : LTL i) : Engine :=
  match l with
  | ⊤       => let cofix go := HaveOutput (Success IsTrue) go in go
  | ⊥       => let cofix go := HaveOutput (Failure IsTrue) go in go
  | Query v => NeedInput (toPipe ∘ v)
  | ¬ p     => Pipe_map (fun x =>
                           match x with
                           | Success s => Failure s
                           | Failure f => Success f
                           end)
                        (toPipe p)
  | p ∧ q   => toPipe p ⨂ toPipe q
  | p ∨ q   => Done (Failure IsTrue)
  | X p     => Pipe_map (Result_map NextFwd) (NeedInput (const (toPipe p)))
  | p U q   => Done (Failure IsTrue)
  | ◇ p     => Done (Failure IsTrue)
  (* | □ p     => let cofix go := fmap AlwaysPrf1 <$> p <*> go in go *)
  | □ p     => Done (Failure IsTrue)
  end.

End Pipe.
