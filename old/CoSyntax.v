Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Coq.Classes.CEquivalence
  Coq.Classes.CRelationClasses
  Coq.Classes.CMorphisms
  FunInd
  Stream
  Bool
  LTL
  Model.

Open Scope program_scope.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Module LTL (S : StreamType).

Module Import L := StreamLTL S.

(** This data type encodes the syntax of LTL in Positive Normal Form (PNF). *)
Inductive Formula : Type :=
  | Top
  | Bottom
  | Examine       (v   : S.a -> Formula)
  | And           (p q : Formula)
  | Or            (p q : Formula)
  | Next          (p   : Formula)
  | Until         (p q : Formula)
  | Release       (p q : Formula)
  | Always        (p   : Formula)
  | Eventually    (p   : Formula)
  | Wait          (p q : Formula)
  | StrongRelease (p q : Formula).

Fixpoint denote (l : Formula) : L.t :=
  match l with
  | Top               => true
  | Bottom            => false
  | Examine v         => fun s => denote (v (head s)) s
  | And p q           => denote p ∧ denote q
  | Or p q            => denote p ∨ denote q
  | Next p            => ◯ (denote p)
  | Until p q         => (denote p) U (denote q)
  | Release p q       => (denote p) R (denote q)
  | Always p          => □ (denote p)
  | Eventually p      => ◇ (denote p)
  | Wait p q          => (denote p) W (denote q)
  | StrongRelease p q => (denote p) M (denote q)
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
  | Release p q       => 1 + size p + size q
  | Always p          => 1 + size p
  | Eventually p      => 1 + size p
  | Wait p q          => 1 + size p + size q
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
  | Release p q       => Until (negate p) (negate q)
  | Always p          => Eventually (negate p)
  | Eventually p      => Always (negate p)
  | Wait p q          => StrongRelease (negate p) (negate q)
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
  | Release p q       => And (expand q) (Or (expand p) (Next (Release p q)))
  | Always p          => And (expand p) (Next (Always p))
  | Eventually p      => Or (expand p) (Next (Eventually p))
  | Wait p q          => Or (expand q) (And (expand p) (Next (Wait p q)))
  | StrongRelease p q => And (expand q) (Or (expand p) (Next (StrongRelease p q)))
  end.

Definition basic (l : Formula) : Prop :=
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

Fixpoint shallow (l : Formula) : Prop :=
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

Lemma expand_complete (l : Formula) : shallow (expand l).
Proof. induction l; simpl in *; intuition auto. Qed.

(** Prune out any instances of Top or Bottom *)
Function prune (l : Formula) : Formula :=
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

CoInductive matches : Formula -> Stream S.a -> Type :=
  | MatchTop s :
      matches Top s
  | MatchExamine v x xs :
      matches (v x) (Cons x xs) -> matches (Examine v) (Cons x xs)
  | MatchAnd p q s :
      matches p s -> matches q s -> matches (And p q) s
  | MatchOrLeft p q s :
      matches p s -> matches (Or p q) s
  | MatchOrRight p q s :
      matches q s -> matches (Or p q) s
  | MatchNext p x xs :
      matches p xs -> matches (Next p) (Cons x xs)
  | MatchUntilTerm p q s :
      matches q s ->
      matches (Until p q) s
  | MatchUntilCont p q x xs :
      matches p (Cons x xs) ->
      matches (Until p q) xs ->
      matches (Until p q) (Cons x xs)
  | MatchAlways p x xs :
      matches p (Cons x xs) ->
      matches (Always p) xs ->
      matches (Always p) (Cons x xs)
  | MatchEventuallyTerm p s :
      matches p s ->
      matches (Eventually p) s
  | MatchEventuallyCont p x xs :
      matches (Eventually p) xs ->
      matches (Eventually p) (Cons x xs)
  | MatchReleaseTerm p q s :
      matches q s ->
      matches p s ->
      matches (Release p q) s
  | MatchReleaseCont p q x xs :
      matches q (Cons x xs) ->
      matches (Release p q) xs ->
      matches (Release p q) (Cons x xs)
  | MatchWaitTerm p q s :
      matches q s ->
      matches (Wait p q) s
  | MatchWaitCont p q x xs :
      matches p (Cons x xs) ->
      matches (Wait p q) xs ->
      matches (Wait p q) (Cons x xs)
  | MatchStrongReleaseTerm p q s :
      matches q s ->
      matches p s ->
      matches (StrongRelease p q) s
  | MatchStrongReleaseCont p q x xs :
      matches q (Cons x xs) ->
      matches (StrongRelease p q) xs ->
      matches (StrongRelease p q) (Cons x xs).

CoInductive Maybe (A : Type) :=
  | Nothing : Maybe A
  | Just    : A -> Maybe A.

Arguments Nothing {A}.
Arguments Just {A} _.

CoFixpoint analyze (l : Formula) (s : Stream S.a) : Maybe (matches l s) :=
  match l with
  | Top    => Just (MatchTop s)
  | Bottom => Nothing

  | Examine v =>
    match s with
    | Cons x xs =>
      match analyze (v x) (Cons x xs) with
      | Just r => Just (MatchExamine v x xs r)
      | Nothing   => Nothing
      end
    end

  | And p q =>
    match analyze p s with
    | Just r =>
      match analyze q s with
      | Just t => Just (MatchAnd p q s r t)
      | Nothing   => Nothing
      end
    | Nothing   => Nothing
    end

  | Or p q  =>
    match analyze p s with
    | Just r => Just (MatchOrLeft p q s r)
    | Nothing   =>
      match analyze q s with
      | Just t => Just (MatchOrRight p q s t)
      | Nothing   => Nothing
      end
    end

  | Next p =>
    match s with
    | Cons x xs =>
      match analyze p xs with
      | Just r => Just (MatchNext p x xs r)
      | Nothing   => Nothing
      end
    end

  | Until p q =>
    let cofix go s : Maybe (matches (Until p q) s) :=
        match analyze q s with
        | Just r  => Just (MatchUntilTerm p q s r)
        | Nothing =>
          match s with
          | Cons x xs =>
            match analyze p (Cons x xs) with
            | Just r =>
              match go xs with
              | Just t  => Just (MatchUntilCont p q x xs r t)
              | Nothing => Nothing
              end
            | Nothing => Nothing
            end
          end
        end in go s

  | Release p q =>
    let cofix go s :=
        match s with
        | Cons _ xs => analyze q s /\ (analyze p s \/ go xs)
        end in go s

  | Always p =>
    let cofix go s :=
        match s with
        | Cons _ xs => analyze p s /\ go xs
        end in go s

  | Eventually p =>
    let cofix go s :=
        match s with
        | Cons _ xs => analyze p s \/ go xs
        end in go s

  | Wait p q =>
    let cofix go s :=
        match s with
        | Cons _ xs => analyze q s \/ (analyze p s /\ go xs)
        end in go s

  | StrongRelease p q =>
    let cofix go s :=
        match s with
        | Cons _ xs => analyze q s /\ (analyze p s \/ go xs)
        end in go s
  end.

Notation "t ⊢ l ⇝ p" := (analyze l t <-> p) (at level 100).

Section matches_coind.

Variable P : Formula -> Stream S.a -> Type.

Hypothesis Bottom_case        : forall s, P Bottom s -> False.
Hypothesis Examine_case       : forall s v, P (Examine v) s -> P (v (head s)) s.
Hypothesis And_case           : forall s p q, P (And p q) s -> P p s * P q s.
Hypothesis Or_case            : forall s p q, P (Or  p q) s -> P p s + P q s.
Hypothesis Next_case          : forall s p, P (Next p) s -> P p (tail s).
Hypothesis Until_case         : forall s p q,
  P (Until p q) s -> P q s + (P p s * P (Until p q) (tail s)).
Hypothesis Release_case       : forall s p q,
  P (Release p q) s -> P q s * (P p s + P (Release p q) (tail s)).
Hypothesis Always_case        : forall s p, P (Always p) s -> P p s * P (Always p) (tail s).
Hypothesis Eventually_case    : forall s p, P (Eventually p) s -> P p s + P (Eventually p) (tail s).
(* Hypothesis Wait_case          : forall s p q, P (Next p) s -> P p (tail s). *)
(* Hypothesis StrongRelease_case : forall s p q, P (Next p) s -> P p (tail s). *)

Theorem matches_coind : forall p s, P p s -> matches p s.
Proof.
  cofix matches_coind.
  destruct p; intros.
  - now constructor.
  - contradiction (Bottom_case _ X).
  - destruct s.
    constructor.
    apply Examine_case in X.
    now apply matches_coind.
  - apply And_case in X.
    destruct X.
    constructor;
    now apply matches_coind.
  - apply Or_case in X.
    destruct X;
    constructor;
    now apply matches_coind.
  - apply Next_case in X.
    destruct s.
    constructor.
    rewrite tail_cons in X.
    now apply matches_coind.
  - apply Until_case in X.
    destruct X.
    + apply MatchUntilTerm.
      now apply matches_coind.
    + destruct p.
      destruct s.
      apply MatchUntilCont;
      now apply matches_coind.
  - apply Release_case in X.
    destruct X.
    destruct s0.
    + apply MatchReleaseTerm;
      now apply matches_coind.
    + destruct s.
      apply MatchReleaseCont;
      now apply matches_coind.
  - apply Always_case in X.
    destruct X.
    destruct s.
    constructor;
    rewrite tail_cons in p1;
    now apply matches_coind.
  - apply Eventually_case in X.
    destruct X.
    + apply MatchEventuallyTerm.
      now apply matches_coind.
    + destruct s.
      apply MatchEventuallyCont.
      now apply matches_coind.
  - admit.
  - admit.
Admitted.

End matches_coind.

Theorem matches_denote p s : matches p s -> denote p s.
Proof.
  intros.
  generalize dependent s.
  induction p; intros.
  + now constructor.
  + inv X.
  + inv X.
    simpl.
    now apply H.
  + inv X.
    now split; intuition.
  + inv X.
    * now left; intuition.
    * now right; intuition.
  + simpl; unfold next.
    inv X.
    simpl.
    now intuition.
  + inv X.
    * exists 0.
      split; auto; lia.
    * admit.
Admitted.

(*
Theorem matches_denote p s : matches p s -> denote p s.
Proof.
  intros.
  induction X; intuition.
  + now constructor.
  + now split.
  + now left.
  + now right.
  + exists 0.
    split; auto; intros.
    lia.
  + inv IHX2.
    destruct H.
    exists (S x0).
    rewrite from_cons.
    split; auto; intros.
    induction i.
    * exact IHX1.
    * rewrite from_cons.
      now intuition.
  + intro.
    generalize dependent xs.
    induction i; intros.
    * exact IHX1.
    * rewrite from_cons.
      now intuition.
  + exists 0.
    exact IHX.
  + destruct IHX.
    exists (S x0).
    now rewrite from_cons.
  + simpl; unfold release, wait.
    right.
    exists 0.
    split.
    * now split.
    * lia.
  + simpl; unfold release, wait.
    clear X1 X2.
    inv IHX2.
    * left.
      intro.
      generalize dependent xs.
      induction i; intros.
      ** exact IHX1.
      ** rewrite from_cons.
         now apply H.
    * right.
      inv H.
      destruct H0.
      inv H.
      exists (S x0).
      rewrite from_cons.
      split.
      ** now split.
      ** generalize dependent xs.
         induction i; intros.
         *** exact IHX1.
         *** rewrite from_cons.
             now apply H0; lia.
  + simpl; unfold wait.
    right.
    exists 0.
    split; auto; intros.
    lia.
  + simpl; unfold wait.
    inv IHX2.
    * left.
      intro.
      generalize dependent xs.
      induction i; intros.
      ** exact IHX1.
      ** rewrite from_cons.
         now apply H.
    * inv H.
      destruct H0.
      right.
      exists (S x0).
      rewrite from_cons.
      split; auto; intros.
      induction i.
      ** exact IHX1.
      ** rewrite from_cons.
         now intuition.
  + simpl; unfold strong_release.
    exists 0.
    split.
    * now split.
    * lia.
  + simpl; unfold strong_release.
    clear X1 X2.
    inv IHX2.
    destruct H.
    inv H.
    exists (S x0).
    rewrite from_cons.
    split; auto; intros.
    * now split.
    * generalize dependent xs.
      induction i; intros.
      ** exact IHX1.
      ** rewrite from_cons.
         now intuition.
Qed.
*)

Definition f_impl (p q : Formula) := forall s, matches p s -> matches q s.

Definition f_eqv (p q : Formula) : Type := f_impl p q * f_impl q p.

Arguments f_impl p q /.
Arguments f_eqv p q /.

Program Instance matches_respects_implies :
  Proper (f_impl ==> stream_eq S.a ==> Basics.arrow) matches.
Next Obligation.
  unfold f_impl.
  repeat intro.
  apply X; clear X.
  generalize dependent y0.
  generalize dependent x0.
  induction x; intros.
  - now constructor.
  - now inv X1.
  - inv X1.
    destruct y0.
    constructor.
    eapply X; eauto.
    now inv X0.
  - inv X1.
    constructor;
    now intuition eauto.
  - inv X1.
    + now constructor; intuition eauto.
    + now constructor; intuition eauto.
  - inv X1.
    destruct y0.
    constructor.
    eapply IHx; eauto.
    now inv X0.
Admitted.

Program Instance matches_respects_equivalent :
  Proper (equivalent ==> eq ==> iff) matches.
Next Obligation.
  split; repeat intro; subst.
  - now apply H.
  - now apply H.
Qed.

(* #[local] Obligation Tactic := induct. *)

Program Instance Examine_respects_implies :
  Proper ((eq ==> implies) ==> implies) Examine.
Next Obligation.
  repeat intro.
  inv H0.
  constructor.
  unfold respectful in H.
  rewrite <- H.

Program Instance Examine_respects_equivalent :
  Proper ((eq ==> equivalent) ==> equivalent) Examine.

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

Program Instance Release_respects_implies :
  Proper (implies ==> implies ==> implies) Release.

Program Instance Release_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) Release.

Program Instance Always_respects_implies :
  Proper (implies ==> implies) Always.

Program Instance Always_respects_equivalent :
  Proper (equivalent ==> equivalent) Always.

Program Instance Eventually_respects_implies :
  Proper (implies ==> implies) Eventually.

Program Instance Eventually_respects_equivalent :
  Proper (equivalent ==> equivalent) Eventually.

Program Instance Wait_respects_implies :
  Proper (implies ==> implies ==> implies) Wait.

Program Instance Wait_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) Wait.

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
  - apply matches_negate.
    apply matches_negate in H0.
    now firstorder.
  - apply matches_negate.
    apply matches_negate in H0.
    now firstorder.
Qed.

Program Instance not_respects_implies : Proper (implies --> implies) not | 1.
Next Obligation.
  - unfold not in *.
    apply matches_negate.
    apply matches_negate in H0.
    now firstorder.
  - unfold not in *.
    apply matches_negate.
    apply matches_negate in H0.
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
Instance eventually_respects_implies :
  Proper (implies ==> implies) eventually := Eventually_respects_implies.
Instance always_respects_implies :
  Proper (implies ==> implies) always := Always_respects_implies.
Instance wait_respects_implies :
  Proper (implies ==> implies ==> implies) wait := Wait_respects_implies.
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

Theorem (* 13 *) until_right_or p q r : (p U r) ∨ (q U r) ⟹ (p ∨ q) U r.
Proof. now induct. Qed.

Theorem (* 14 *) until_left_and p q r : p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Proof. now induct. Qed.

Theorem (* NEW *) until_or_until p q r s : (p ∧ r) U (q ∨ s) ⟹ (p U q) ∨ (r U s).
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

Lemma matches_wait x xs p q :
  matches (Wait p q) (x :: xs) <->
  matches q (x :: xs) \/ (matches p (x :: xs) /\ matches (Wait p q) xs).
Proof. reflexivity. Qed.

Lemma matches_strongrelease x xs p q :
  matches (StrongRelease p q) (x :: xs) <->
  matches q (x :: xs) /\ (matches p (x :: xs) \/ matches (StrongRelease p q) xs).
Proof. reflexivity. Qed.

Theorem (* 18 *) until_right_and_order p q r : p U (q ∧ r) ⟹ (p U q) U r.
Proof.
  unfold until, and.
  repeat intro;
  induction s; intuition.
  - now simpl in *; intuition.
  - rewrite matches_until, matches_and in *.
    firstorder.
    destruct (classic (matches r (a :: s))); auto.
    right; split; auto.
    destruct (classic (matches q (a :: s))); auto.
      now left.
    rewrite matches_until in *.
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
