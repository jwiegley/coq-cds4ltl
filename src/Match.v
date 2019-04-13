Require Import
  Program
  Coq.Lists.List
  Coq.Classes.Equivalence
  Coq.omega.Omega
  Coq.Sets.Ensembles.

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

Definition option_map {a b} (f : a -> b) (mx : option a) : option b :=
  match mx with
  | None => None
  | Some x => Some (f x)
  end.

Infix "<$>" := option_map (at level 40).

Definition option_ap {a b} (mf : option (a -> b)) (mx : option a) : option b :=
  match mf, mx with
  | None, _        => None
  | _, None        => None
  | Some f, Some x => Some (f x)
  end.

Infix "<*>" := option_ap (at level 40).

Definition option_join {a} (mx : option (option a)) : option a :=
  match mx with
  | None => None
  | Some None => None
  | Some (Some x) => Some x
  end.

Definition option_bind {a b} (mx : option a) (f : a -> option b) : option b :=
  match mx with
  | None => None
  | Some x => f x
  end.

Infix ">>=" := option_bind (at level 50).

Definition option_alt {a} (mx : option a) (my : option a) : option a :=
  match mx with
  | None => my
  | _    => mx
  end.

Infix "<|>" := option_alt (at level 50).

Lemma fmap_endo_some {c} (f : c -> c) (m : option c) (x : c) :
  f <$> m = Some x <-> exists y, x = f y /\ m = Some y.
Proof.
  induction m; simpl; split; intros.
  - inversion_clear H.
    eexists; eauto.
  - destruct H, H; subst.
    now inversion_clear H0.
  - discriminate.
  - destruct H, H; discriminate.
Qed.

Lemma fmap_endo_none {c} (f : c -> c) (m : option c) :
  f <$> m = None <-> m = None.
Proof. induction m; simpl; intuition auto; discriminate. Qed.

Lemma ap_endo_some {c} (f : c -> c -> c) (m n : option c) (x : c) :
  f <$> m <*> n = Some x
    <-> exists y z, x = f y z /\ m = Some y /\ n = Some z.
Proof.
  induction m, n; simpl; split; intros.
  - inversion_clear H.
    eexists; eauto.
  - destruct H, H, H, H0; subst.
    inversion_clear H0.
    now inversion_clear H1.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
Qed.

Lemma ap_endo_none {c} (f : c -> c -> c) (m n : option c) :
  f <$> m <*> n = None <-> m = None \/ n = None.
Proof. induction m, n; simpl; intuition auto; discriminate. Qed.

Lemma bind_endo_some {c} (f : c -> option c) (m : option c) (x : c) :
  m >>= f = Some x <-> exists y, f y = Some x /\ m = Some y.
Proof.
  unfold option_bind.
  induction m; simpl; split; intros.
  - now firstorder eauto.
  - destruct H, H.
    now inversion_clear H0.
  - discriminate.
  - destruct H, H.
    discriminate.
Qed.

Lemma bind_endo_none {c} (f : c -> option c) (m : option c) :
  m >>= f = None <-> m = None \/ exists y, f y = None /\ m = Some y.
Proof.
  induction m; simpl; split; intros.
  - now right; eauto.
  - destruct H.
      discriminate.
    firstorder eauto.
    now inversion_clear H0.
  - now left.
  - reflexivity.
Qed.

Lemma alt_endo_some {c} (m n : option c) (x : c) :
  m <|> n = Some x <-> m = Some x \/ (m = None /\ n = Some x).
Proof.
  unfold option_alt.
  induction m; simpl; intuition auto; discriminate.
Qed.

Lemma alt_endo_none {c} (m n : option c) :
  m <|> n = None <-> m = None /\ n = None.
Proof. induction m, n; simpl; intuition auto; discriminate. Qed.

Fixpoint compare (t : option term) (l : LTL a) (s : Stream a) :=
  match l return option Match with
  | ⊤       => Some IsTrue
  | ⊥       => None

  | Query v => match s with
               | []     => EndOfTrace (Query v) <$> t
               | x :: _ => compare t (v x) s
               end

  | ¬ p     => match compare t p s with
               | None   => Some Negated
               | Some _ => None
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
                   | []      => Some AlwaysPrf2
                   | x :: xs => AlwaysPrf1 <$> compare t p (x :: xs)
                                           <*> go xs
                   end in go s
  end.

Lemma compare_correct (L : LTL a) (T : Stream a) :
  forall t,
    (exists P, compare t L T = Some P)
      <-> matches a (match t with None => False | _ => True end) L T.
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
      apply fmap_endo_some in H.
      now firstorder eauto.
    + destruct T, t; simpl in *; auto;
      [ eexists; eauto | contradiction | .. ];
      apply IHL in H;
      destruct H;
      exists (NextFwd x);
      apply fmap_endo_some;
      exists x; auto.
  - split; intros;
    induction T; simpl in *; auto.
    + destruct H, t; auto; discriminate.
    + destruct H.
      apply alt_endo_some in H.
      destruct H; intuition auto.
      * apply fmap_endo_some in H.
        destruct H, H; subst.
        left.
        apply IHL2.
        now firstorder eauto.
      * apply fmap_endo_none in H0.
        apply ap_endo_some in H1.
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
      apply alt_endo_some in H.
      destruct H.
      * apply fmap_endo_some in H.
        destruct H, H; subst.
        now firstorder eauto.
      * destruct H.
        apply fmap_endo_some in H0.
        destruct H0, H0; subst.
        now firstorder eauto.
    + destruct t; auto; simpl.
        now eexists; eauto.
      contradiction.
    + destruct H.
        apply IHL in H.
        destruct H.
        eexists.
        apply alt_endo_some.
        left.
        apply fmap_endo_some.
        now firstorder eauto.
      intuition.
      destruct H0.
      rewrite H0; clear H0.
      destruct (compare t L (a0 :: T)) eqn:?.
        eexists.
        apply alt_endo_some.
        now left; simpl; auto.
      eexists.
      apply alt_endo_some.
      now right; split; auto.
  - split; intros;
    induction T; simpl in *; auto.
    + destruct H.
      apply ap_endo_some in H.
      destruct H, H, H, H0.
      now firstorder eauto.
    + now eexists; eauto.
    + destruct H.
      intuition.
      destruct H1.
      apply IHL in H.
      destruct H.
      eexists.
      apply ap_endo_some.
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

Variable t : option term.

Notation "T ⊢ L ⟿ P" := (compare t L T = Some P) (at level 80).

Definition Match_equiv (p q : Match) : Prop := p = q.

Ltac end_of_trace := apply EndOfTrace; [auto|intro; discriminate].

Lemma match_neg P T φ : (T ⊢ ¬φ ⟿ P) <-> ~ (T ⊢ φ ⟿ P).
Proof.
Abort.

End Match.

Section Examples.

Open Scope ltl_scope.

Example ex_compare_sample :
  compare nat () None (□ (ifThen (fun n => n =? 3)
                                 (fun n => X (◇ (num (n + 5))))))
          [1; 2; 3; 4; 5; 6; 7; 8; 9]
    = Some
        (AlwaysPrf1 nat () (IsTrue nat ())
           (AlwaysPrf1 nat () (IsTrue nat ())
              (AlwaysPrf1 nat ()
                 (NextFwd nat ()
                    (EventuallyFwd nat ()
                       (EventuallyFwd nat ()
                          (EventuallyFwd nat ()
                             (EventuallyFwd nat ()
                                (EventuallyStop nat () (IsTrue nat ())))))))
                 (AlwaysPrf1 nat () (IsTrue nat ())
                    (AlwaysPrf1 nat () (IsTrue nat ())
                       (AlwaysPrf1 nat () (IsTrue nat ())
                          (AlwaysPrf1 nat () (IsTrue nat ())
                             (AlwaysPrf1 nat () (IsTrue nat ())
                                (AlwaysPrf1 nat () (IsTrue nat ())
                                   (AlwaysPrf2 nat ())))))))))).
Proof. reflexivity. Qed.

End Examples.
