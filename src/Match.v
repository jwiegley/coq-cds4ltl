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
  | EndOfTrace     (l : LTL a b) (t : term)
  | IsTrue
  | Base           (x : b)
  | Negated
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

Fixpoint compare (t : option term) (l : LTL a b) (s : Stream a) : option Match :=
  match l with
  | ⊤ => Some IsTrue
  | ⊥ => None

  | Query v =>
    match s with
    | []     => EndOfTrace (Query v) <$> t
    | x :: _ => Base <$> v (option b) x Some None
    end

  | ¬ p =>
    match compare t p s with
    | None => Some Negated
    | Some _ => None
    end

  | p ∧ q => Both    <$> compare t p s <*> compare t q s
  | p ∨ q => InLeft  <$> compare t p s
         <|> InRight <$> compare t q s

  | p → q =>
    match compare t p s with
    | None   => Some NotImplied
    | Some P => Implied P <$> compare t q s
    end

  | X p =>
    match s with
    | []      => EndOfTrace (X p) <$> t
    | _ :: xs => NextFwd <$> compare t p xs
    end

  | p U q =>
    let fix go s :=
        match s with
        | []      => EndOfTrace (p U q) <$> t
        | x :: xs => UntilPrf1 <$> compare t q (x :: xs)
                 <|> compare t p (x :: xs) >>=
                     (fun P => UntilPrf3 P <$> go xs <|> Some (UntilPrf2 P))
        end in go s

  | ◇ p =>
    let fix go s :=
        match s with
        | []      => EndOfTrace (◇ p) <$> t
        | x :: xs => EventuallyStop <$> compare t p (x :: xs)
                 <|> EventuallyFwd  <$> go xs
        end in go s

  | □ p =>
    let fix go s :=
        match s with
        | []      => Some AlwaysPrf2
        | x :: xs => AlwaysPrf1 <$> compare t p (x :: xs) <*> go xs
        end in go s
  end.

Lemma compare_correct (L : LTL a b) (T : Stream a) :
  forall (t : option term),
    (forall x b' v,
                L = Query v ->
                v (option b) x Some None = Some b' ->
                v Prop x (const True) False) ->
    (exists (P : Match), compare t L T = Some P)
      <-> matches a b (match t with None => False | _ => True end) L T.
Proof.
  split;
  induction L;
  simpl; intros;
  try destruct H0;
  auto; try discriminate;
  destruct T, t;
  simpl in *;
  auto; try discriminate.
  admit.
  admit.
Abort.

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
  | DepUntilPrf1      p `(Q : MatchDep q)                        : MatchDep (p U q)
  | DepUntilPrf2      `(P : MatchDep p) `(PS : MatchDep (p U q)) : MatchDep (p U q)
  | DepUntilPrf3      `(P : MatchDep p) q                        : MatchDep (p U q)
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