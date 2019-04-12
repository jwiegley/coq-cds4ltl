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
Variable b : Type.              (* The type of data derived from each entry *)
Variable term : Type.

Inductive Match : Type :=
  | EndOfTrace     (t : term)
  | IsTrue
  | Base           (x : b)
  | Both           (p q : Match)
  | InLeft         (p : Match)
  | InRight        (q : Match)
  | NotImplied
  | Implied        (p q : Match)
  | NextFwd        (p : Match)
  | EventuallyStop (p : Match)
  | EventuallyFwd  (p : Match)
  | UntilPrf1      (q : Match)
  | UntilPrf2      (p : Match)
  | UntilPrf3      (p : Match) (ps : Match)
  | AlwaysPrf1     (p : Match) (ps : Match)
  | AlwaysPrf2.

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
  | DepUntilPrf1      p `(Q : MatchDep q)                        : MatchDep (p U q)
  | DepUntilPrf2      `(P : MatchDep p) `(PS : MatchDep (p U q)) : MatchDep (p U q)
  | DepUntilPrf3      `(P : MatchDep p) q                        : MatchDep (p U q)
  | DepAlwaysPrf1     `(P : MatchDep p) `(PS : MatchDep (□ p))   : MatchDep (□ p)
  | DepAlwaysPrf2     p                                          : MatchDep (□ p).

Equations compare (t : option term) (L : LTL) (T : Stream) : option Match
  by wf (remaining L T) lt :=

  compare t (⊤) _ := Some IsTrue;
  compare t (⊥) _ := None;

  compare t (Query v) (x :: _) :=
    match v x with
    | None => None
    | Some r => Some (Base r)
    end;

  compare t (Query v) [] :=
    match t with
    | None => None
    | Some t => Some (EndOfTrace t)
    end;

  compare t (And p q) T :=
    match compare t p T with
    | None   => None
    | Some P =>
      match compare t q T with
      | None   => None
      | Some Q => Some (Both P Q)
      end
    end;

  compare t (Or p q) T :=
    match compare t p T with
    | None   =>
      match compare t q T with
      | None   => None
      | Some Q => Some (InRight Q)
      end
    | Some P => Some (InLeft P)
    end;

  compare t (Impl p q) T :=
    match compare t p T with
    | None   => Some NotImplied
    | Some P =>
      match compare t q T with
      | None   => None
      | Some Q => Some (Implied P Q)
      end
    end;

  compare t (Next p) (_ :: xs) :=
    match compare t p xs with
    | None => None
    | Some P => Some (NextFwd P)
    end;

  compare t (Next p) [] :=
    match t with
    | None => None
    | Some t => Some (EndOfTrace t)
    end;

  compare t (Eventually p) (x :: xs) :=
    match compare t p (x :: xs) with
    | None =>
      match compare t p xs with
      | None => None
      | Some P => Some (EventuallyFwd P)
      end
    | Some P => Some (EventuallyStop P)
    end;

  compare t (Eventually p) [] :=
    match t with
    | None => None
    | Some t => Some (EndOfTrace t)
    end;

  compare t (Until p q) (x :: xs) :=
    match compare t q (x :: xs) with
    | Some Q => Some (UntilPrf1 Q)
    | None =>
      match xs with
      | [] =>
        match compare t p [x] with
        | Some P => Some (UntilPrf2 P)
        | None => None
        end
      | _ =>
        match compare t p (x :: xs) with
        | None => None
        | Some P =>
          match compare t (p U q) xs with
          | Some Q => Some (UntilPrf3 P Q)
          | None => None
          end
        end
      end
    end;

  compare t (Until p q) [] :=
    match t with
    | None => None
    | Some t => Some (EndOfTrace t)
    end;

  compare t (Always p) (x :: xs) :=
    match compare t p (x :: xs) with
    | None => None
    | Some P =>
      match compare t (Always p) xs with
      | None => None
      | Some PS => Some (AlwaysPrf1 P PS)
      end
    end;

  compare t (Always p) [] := Some AlwaysPrf2.

Ltac simplify_compare :=
  repeat rewrite
    ?compare_equation_1,
    ?compare_equation_2,
    ?compare_equation_3,
    ?compare_equation_4,
    ?compare_equation_5,
    ?compare_equation_6,
    ?compare_equation_7,
    ?compare_equation_8,
    ?compare_equation_9,
    ?compare_equation_10,
    ?compare_equation_11,
    ?compare_equation_12,
    ?compare_equation_13,
    ?compare_equation_14,
    ?compare_equation_15.

Ltac simplify_compare_in H :=
  repeat rewrite
    ?compare_equation_1,
    ?compare_equation_2,
    ?compare_equation_3,
    ?compare_equation_4,
    ?compare_equation_5,
    ?compare_equation_6,
    ?compare_equation_7,
    ?compare_equation_8,
    ?compare_equation_9,
    ?compare_equation_10,
    ?compare_equation_11,
    ?compare_equation_12,
    ?compare_equation_13,
    ?compare_equation_14,
    ?compare_equation_15
    in H.

Lemma compare_and_inv t L1 L2 T P :
  compare t (L1 ∧ L2) T = Some P ->
  exists P1 P2, P = Both P1 P2
    /\ compare t L1 T = Some P1 /\ compare t L2 T = Some P2.
Proof.
  intros H.
  simplify_compare_in H.
  destruct (compare t L1 T) eqn:?; [|discriminate].
  destruct (compare t L2 T) eqn:?; [|discriminate].
  exists m, m0.
  now inversion H; subst; clear H.
Qed.

Lemma compare_and_impl t L1 L2 T P1 P2 :
  compare t L1 T = Some P1 -> compare t L2 T = Some P2 ->
  compare t (L1 ∧ L2) T = Some (Both P1 P2).
Proof.
  intros.
  simplify_compare.
  now rewrite H, H0.
Qed.

Lemma compare_or_inv t L1 L2 T P :
  compare t (L1 ∨ L2) T = Some P ->
    (exists P1, P = InLeft P1 /\ compare t L1 T = Some P1) \/
    (exists P2, P = InRight P2 /\ compare t L2 T = Some P2).
Proof.
  intros H.
  simplify_compare_in H.
  destruct (compare t L1 T) eqn:?.
    left.
    exists m.
    now inversion H; subst; clear H.
  destruct (compare t L2 T) eqn:?; [|discriminate].
  right.
  exists m.
  now inversion H; subst; clear H.
Qed.

Lemma compare_or_left_impl t L1 L2 T P1 :
  compare t L1 T = Some P1 ->
  compare t (L1 ∨ L2) T = Some (InLeft P1).
Proof.
  intros.
  simplify_compare.
  now rewrite H.
Qed.

Lemma compare_or_right_impl t L1 L2 T P2 :
  compare t L1 T = None ->
  compare t L2 T = Some P2 ->
  compare t (L1 ∨ L2) T = Some (InRight P2).
Proof.
  intros.
  simplify_compare.
  now rewrite H, H0.
Qed.

Lemma compare_impl_inv t L1 L2 T P :
  compare t (L1 → L2) T = Some P ->
  (exists P1 P2, P = Implied P1 P2
     /\ compare t L1 T = Some P1 /\ compare t L2 T = Some P2) \/
  (P = NotImplied /\ compare t L1 T = None).
Proof.
  intros H.
  simplify_compare_in H.
  destruct (compare t L1 T) eqn:?.
    destruct (compare t L2 T) eqn:?; [|discriminate].
    left.
    exists m, m0.
    now inversion H; subst; clear H.
  right.
  now inversion H; subst; clear H.
Qed.

Lemma compare_impl_fails_impl t L1 L2 T :
  compare t L1 T = None ->
  compare t (L1 → L2) T = Some NotImplied.
Proof.
  intros.
  simplify_compare.
  now rewrite H.
Qed.

Lemma compare_impl_holds_impl t L1 L2 T P1 P2 :
  compare t L1 T = Some P1 -> compare t L2 T = Some P2 ->
  compare t (L1 → L2) T = Some (Implied P1 P2).
Proof.
  intros.
  simplify_compare.
  now rewrite H, H0.
Qed.

Lemma Compute_Verified (t : option term) (L : LTL) (T : Stream) :
  (exists P, compare t L T = Some P) <-> matches L T.
Proof.
  induction L; simpl; split; intros.
  - simplify_compare_in H; now constructor.
  - simplify_compare; now eauto.
  - simplify_compare_in H.
    destruct H.
    discriminate.
  - simplify_matches_in H.
    contradiction.
  - destruct H.
    induction T; simplify_compare_in H.
      destruct t; [|discriminate].
      now simplify_matches.
    destruct (v a0) eqn:?; [|discriminate].
    simplify_matches.
    inversion H; subst; clear H.
    now exists b0.
  - admit.
  - destruct H.
    apply matches_and.
    apply compare_and_inv in H.
    repeat destruct H.
    destruct H0.
    split.
      now apply IHL1; eauto.
    now apply IHL2; eauto.
  - admit.
  - destruct H.
    apply matches_or.
    apply compare_or_inv in H.
    repeat destruct H.
      left.
      now apply IHL1; eauto.
    right.
    now apply IHL2; eauto.
  - admit.
  - destruct H.
    apply matches_impl; intros.
    apply compare_impl_inv in H.
    destruct H.
      repeat destruct H.
      apply IHL2.
      now exists x1.
    apply IHL1 in H0.
    destruct H, H0.
    rewrite H1 in H0.
    discriminate.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Variable t : option term.

Notation "T ⊢ L ⟿ P" := (compare t L T = Some P) (at level 80).

Definition Match_equiv (p q : Match) : Prop := p = q.

Ltac end_of_trace := apply EndOfTrace; [auto|intro; discriminate].

Lemma match_neg P T φ : (T ⊢ ¬φ ⟿ P) <-> ~ (T ⊢ φ ⟿ P).
Proof.
  split; intros.
    simplify_compare_in H.
    destruct (compare t φ T) eqn:?.
      discriminate.
    intro.
    discriminate.
  simplify_compare.
Abort.

End Match.