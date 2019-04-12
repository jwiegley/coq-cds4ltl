Require Import
  Program
  Coq.Lists.List
  Coq.Classes.Equivalence
  Coq.Logic.Classical
  Coq.omega.Omega
  Coq.Sets.Ensembles.

Require Import Equations.Equations.
Require Import Equations.EqDec.

Open Scope program_scope.
Open Scope list_scope.

Require Import Same_set.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Section LTL.

Variable a : Type.              (* The type of entries in the trace *)
Variable b : Type.              (* The type of data derived from each entry *)

Definition Stream := list a.

Inductive LTL : Type :=
  (* Boolean layer *)
  | Top
  | Bottom
  | Query (v : a -> option b)
  | Not (p : LTL)
  | And (p q : LTL)
  | Or (p q : LTL)
  | Impl (p q : LTL)

  (* Temporal layer *)
  | Next (p : LTL)
  | Eventually (p : LTL)
  | Until (p q : LTL)
  | Always (p : LTL).

Notation "⊤"       := Top             (at level 50).
Notation "⊥"       := Bottom          (at level 50).
Notation "¬ x"     := (Not x)         (at level 50).
Infix    "∧"       := And             (at level 50).
Infix    "∨"       := Or              (at level 50).
Infix    "→"       := Impl            (at level 50).
Notation "'X' x"   := (Next x)        (at level 50).
Notation "◇ x"     := (Eventually x)  (at level 50).
Notation "p 'U' q" := (Until p q)     (at level 50).
Notation "□ x"     := (Always x)      (at level 50).

Fixpoint LTL_size (p : LTL) : nat :=
  match p with
  | Query v      => 1
  | Top          => 1
  | Bottom       => 1
  | Not p        => 1 + LTL_size p
  | And p q      => 1 + LTL_size p + LTL_size q
  | Or p q       => 1 + LTL_size p + LTL_size q
  | Impl p q     => 1 + LTL_size p + LTL_size q
  | Next p       => 1 + LTL_size p
  | Eventually p => 1 + LTL_size p
  | Until p q    => 1 + LTL_size p + LTL_size q
  | Always p     => 1 + LTL_size p
  end.

Definition remaining (p : LTL) (s : Stream) := LTL_size p + length s.

Local Obligation Tactic := program_simpl; unfold remaining; simpl; try omega.

(* [term] is a type that is found at the end of a partial trace match. By
   choosing [False], one can express that formula must exactly match within a
   trace. *)
Variable term : Prop.

(* This define the set of sentences matched by a given LTL formula. *)
Equations matches (l : LTL) (s : Stream) : Prop by wf (remaining l s) lt :=
  matches (⊤)       _         := True;
  matches (⊥)       _         := False;
  matches (Query v) []        := term;
  matches (Query v) (x :: _)  := exists b, v x = Some b;
  matches (¬ p)     s         := ~ matches p s;
  matches (p ∧ q)   s         := matches p s /\ matches q s;
  matches (p ∨ q)   s         := matches p s \/ matches q s;
  matches (p → q)   s         := matches p s -> matches q s;
  matches (X p)     []        := term;
  matches (X p)     (_ :: xs) := matches p xs;
  matches (◇ p)     []        := term;
  matches (◇ p)     (x :: xs) := matches p (x :: xs) \/ matches (◇ p) xs;
  matches (p U q)   []        := term;
  matches (p U q)   (x :: xs) := matches q (x :: xs) \/
                                 (matches p (x :: xs) /\ matches (p U q) xs);
  matches (□ p)     []        := True;
  matches (□ p)     (x :: xs) := matches p (x :: xs) /\ matches (□ p) xs.

Notation matches_equation_top             := matches_equation_1.
Notation matches_equation_bottom          := matches_equation_2.
Notation matches_equation_query_nil       := matches_equation_3.
Notation matches_equation_query_cons      := matches_equation_4.
Notation matches_equation_not             := matches_equation_5.
Notation matches_equation_and             := matches_equation_6.
Notation matches_equation_or              := matches_equation_7.
Notation matches_equation_impl            := matches_equation_8.
Notation matches_equation_fwd_nil         := matches_equation_9.
Notation matches_equation_fwd_cons        := matches_equation_10.
Notation matches_equation_eventually_nil  := matches_equation_11.
Notation matches_equation_eventually_cons := matches_equation_12.
Notation matches_equation_until_nil       := matches_equation_13.
Notation matches_equation_until_cons      := matches_equation_14.
Notation matches_equation_always_nil      := matches_equation_15.
Notation matches_equation_always_cons     := matches_equation_16.

Ltac simplify_matches :=
  repeat rewrite
    ?matches_equation_1,
    ?matches_equation_2,
    ?matches_equation_3,
    ?matches_equation_4,
    ?matches_equation_5,
    ?matches_equation_6,
    ?matches_equation_7,
    ?matches_equation_8,
    ?matches_equation_9,
    ?matches_equation_10,
    ?matches_equation_11,
    ?matches_equation_12,
    ?matches_equation_13,
    ?matches_equation_14,
    ?matches_equation_15,
    ?matches_equation_16.

Ltac simplify_matches_in H :=
  repeat rewrite
    ?matches_equation_1,
    ?matches_equation_2,
    ?matches_equation_3,
    ?matches_equation_4,
    ?matches_equation_5,
    ?matches_equation_6,
    ?matches_equation_7,
    ?matches_equation_8,
    ?matches_equation_9,
    ?matches_equation_10,
    ?matches_equation_11,
    ?matches_equation_12,
    ?matches_equation_13,
    ?matches_equation_14,
    ?matches_equation_15,
    ?matches_equation_16
    in H.

Lemma matches_bottom T :
  matches (⊥) T <-> False.
Proof. induction T; simplify_matches; split; auto. Qed.

Lemma matches_not L T :
  matches (¬ L) T <-> ~ matches L T.
Proof. induction T; simplify_matches; split; auto. Qed.

Lemma matches_contradiction L T :
  matches L T -> matches (¬ L) T -> False.
Proof. induction T; simplify_matches; auto. Qed.

Lemma matches_and L1 L2 T :
  matches (L1 ∧ L2) T <-> matches L1 T /\ matches L2 T.
Proof. induction T; simplify_matches; split; auto. Qed.

Lemma matches_or L1 L2 T :
  matches (L1 ∨ L2) T <-> matches L1 T \/ matches L2 T.
Proof. induction T; simplify_matches; split; auto. Qed.

Lemma matches_impl L1 L2 T :
  matches (L1 → L2) T <-> (matches L1 T -> matches L2 T).
Proof. induction T; simplify_matches; split; auto. Qed.

Lemma matches_next L T x :
  matches (X L) (x :: T) <-> matches L T.
Proof. induction T; simplify_matches; split; auto. Qed.

Lemma matches_eventually L T x :
  matches (◇ L) (x :: T) <-> matches L (x :: T) \/ matches (◇ L) T.
Proof. induction T; simplify_matches; split; auto. Qed.

Lemma matches_until L1 L2 T x :
  matches (L1 U L2) (x :: T) <->
  matches L2 (x :: T) \/
    (matches L1 (x :: T) /\ matches (L1 U L2) T).
Proof. induction T; simplify_matches; split; auto. Qed.

Lemma matches_always L T x :
  matches (□ L) (x :: T) <-> matches L (x :: T) /\ matches (□ L) T.
Proof. induction T; simplify_matches; split; auto. Qed.

Definition impl (φ ψ : LTL) := ¬φ ∨ ψ.

Definition iff (φ ψ : LTL) := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := iff (at level 50).

(* (ψ remains true until and including once φ becomes true.
   If φ never become true, ψ must remain true forever.) *)
Definition release (φ ψ : LTL) := ¬(¬φ U ¬ψ).
Notation "p 'R' q" := (release p q) (at level 50).

Definition ltl_weak_equiv (p q : LTL) : Prop :=
  term -> Same_set _ (matches p) (matches q).
Arguments ltl_weak_equiv p q /.

Infix "≈[weak]" := ltl_weak_equiv (at level 70).

Definition ltl_strong_equiv (p q : LTL) : Prop :=
  (term -> False) -> Same_set _ (matches p) (matches q).
Arguments ltl_strong_equiv p q /.

Infix "≈[strong]" := ltl_strong_equiv (at level 70).

Definition ltl_infinite_equiv (p q : LTL) : Prop :=
  forall T : Stream, length T = S (length T) -> matches p T <-> matches q T.
Arguments ltl_infinite_equiv p q /.

Infix "≈[infinite]" := ltl_infinite_equiv (at level 70).

Infix "≈" := equiv (at level 70).

Program Instance Equivalence_ltl_equiv : Equivalence ltl_weak_equiv.
Next Obligation.
  unfold ltl_weak_equiv.
  repeat intro; auto.
  reflexivity.
Qed.
Next Obligation.
  unfold ltl_weak_equiv.
  repeat intro; intuition auto.
  now symmetry.
Qed.
Next Obligation.
  unfold ltl_weak_equiv.
  repeat intro; intuition auto.
  now transitivity (matches y).
Qed.

Ltac prep :=
  split; repeat intro; unfold In in *;
  match goal with
    [ T : Stream |- _ ] =>
      induction T;
      repeat
        match goal with
        | [ H : matches _ _ |- _ ] => simplify_matches_in H
        | [ |- matches _ _ ] => simplify_matches
        end
  end;
  intuition auto;
  try discriminate.

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof. prep. Qed.

(* ψ always remains true *)
Lemma always_remains (ψ : LTL) : □ ψ ≈[strong] ⊥ R ψ.
Proof.
  prep.
  - unfold release in H.
    now apply matches_contradiction in H4.
  - now apply NNPP in H1.
  - apply IHx.
    now apply matches_not.
Qed.

Lemma always_not_eventually (ψ : LTL) : □ ψ ≈[strong] ¬◇ ¬ψ.
Proof.
  prep.
  - now apply matches_contradiction in H0.
  - now apply NNPP in H1.
  - apply IHx.
    now apply matches_not.
Qed.

Definition weakUntil (φ ψ : LTL) := (φ U ψ) ∨ □ φ.
Notation "p 'W' q" := (weakUntil p q) (at level 50).

Definition strongRelease (φ ψ : LTL) := ψ U (φ ∧ ψ).
Notation "p 'M' q" := (strongRelease p q) (at level 50).

Lemma foo2 (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Proof. prep. Abort.

Lemma foo3 (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Proof. prep. Abort.

Lemma foo4 (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof. prep. Abort.

Lemma foo5 (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Proof. prep. Abort.

Lemma foo6 (φ ψ : LTL) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Proof. prep. Abort.

Lemma foo7 (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Proof. prep. Abort.

Lemma foo8 (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Proof. prep. Abort.

(** Distributivity *)

Lemma foo10 (φ ψ : LTL) : X (φ ∨ ψ) ≈ (X φ) ∨ (X ψ).
Proof. prep. Qed.

Lemma foo11 (φ ψ : LTL) : X (φ ∧ ψ) ≈ (X φ) ∧ (X ψ).
Proof. prep. Qed.

Lemma foo12 (φ ψ : LTL) : X (φ U ψ) ≈ (X φ) U (X ψ).
Proof. prep. Abort.

Lemma foo13 (φ ψ : LTL) : ◇ (φ ∨ ψ) ≈ (◇ φ) ∨ (◇ ψ).
Proof. prep. Abort.

Lemma foo14 (φ ψ : LTL) : □ (φ ∧ ψ) ≈ (□ φ) ∧ (□ ψ).
Proof. prep. Abort.

Lemma foo15 (ρ φ ψ : LTL) : ρ U (φ ∨ ψ) ≈ (ρ U φ) ∨ (ρ U ψ).
Proof. prep. Abort.

Lemma foo16 (ρ φ ψ : LTL) : (φ ∧ ψ) U ρ ≈ (φ U ρ) ∧ (ψ U ρ).
Proof. prep. Abort.

(** Negation propagation *)

Lemma foo18 (φ : LTL) : ¬(X φ) ≈[infinite] X ¬φ.
Proof. prep. Qed.

Lemma foo19 (φ : LTL) : ¬(◇ φ) ≈[strong] □ ¬φ.
Proof.
  prep.
  - apply IHx.
    now apply matches_not.
  - now apply matches_contradiction in H0.
Qed.

Lemma foo20 (φ ψ : LTL) : ¬ (φ U ψ) ≈ (¬φ R ¬ψ).
Proof. prep. Abort.

Lemma foo21 (φ ψ : LTL) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Proof. prep. Abort.

Lemma foo22 (φ : LTL) : ¬(□ φ) ≈ ◇ ¬φ.
Proof. prep. Abort.

Lemma foo23 (φ ψ : LTL) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Proof. prep. Abort.

Lemma foo24 (φ ψ : LTL) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Proof. prep. Abort.

(** Special Temporal properties *)

Lemma foo25 (φ : LTL) :   ◇ φ ≈ ◇ ◇ φ.
Proof. prep. Qed.

Lemma foo26 (φ : LTL) :   □ φ ≈ □ □ φ.
Proof. prep. Qed.

Lemma foo27 (φ ψ : LTL) : φ U ψ ≈ φ U (φ U ψ).
Proof. prep. Qed.

Lemma foo28 (φ ψ : LTL) : φ U ψ ≈[infinite] ψ ∨ (φ ∧ X(φ U ψ)).
Proof. prep. Qed.

Lemma foo29 (φ ψ : LTL) : φ W ψ ≈[infinite] ψ ∨ (φ ∧ X(φ W ψ)).
Proof. prep. Qed.

Lemma foo30 (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ X(φ R ψ)).
Proof. prep. Abort.

Lemma foo31 (φ : LTL) :   □ φ ≈[infinite] φ ∧ X(□ φ).
Proof. prep. Qed.

Lemma foo32 (φ : LTL) :   ◇ φ ≈ φ ∨ X(◇ φ).
Proof. prep. Qed.

End LTL.
