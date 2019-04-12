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
    (* Use a final encoding of [option] as the result, to allow scoping by the
       user of [Query]. *)
  | Query (v : forall r, a -> (b -> r) -> r -> r)
  | Not (p : LTL)
  | And (p q : LTL)
  | Or (p q : LTL)
  | Impl (p q : LTL)

  (* Temporal layer *)
  | Next (p : LTL)
  | Until (p q : LTL)
  | Eventually (p : LTL)
  | Always (p : LTL).

Notation "⊤"       := Top             (at level 50).
Notation "⊥"       := Bottom          (at level 50).
Notation "¬ x"     := (Not x)         (at level 0).
Infix    "∧"       := And             (at level 50).
Infix    "∨"       := Or              (at level 50).
Infix    "→"       := Impl            (at level 50).
Notation "'X' x"   := (Next x)        (at level 0).
Notation "p 'U' q" := (Until p q)     (at level 50).
Notation "◇ x"     := (Eventually x)  (at level 0).
Notation "□ x"     := (Always x)      (at level 0).

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
  | Until p q    => 1 + LTL_size p + LTL_size q
  | Eventually p => 1 + LTL_size p
  | Always p     => 1 + LTL_size p
  end.

Definition remaining (p : LTL) (s : Stream) := LTL_size p + length s.

Local Obligation Tactic := program_simpl; unfold remaining; simpl; try omega.

(* [term] is a type that is found at the end of a partial trace match. By
   choosing [False], one can express that formula must exactly match within a
   trace. *)
Variable term : Prop.

Fixpoint matches (l : LTL) (s : Stream) {struct l} : Prop :=
  match l with
  | ⊤ => True
  | ⊥ => False

  | Query v =>
    match s with
    | []     => term
    | x :: _ => v Prop x (const True) False
    end

  | ¬ p => ~ matches p s

  | p ∧ q => matches p s /\ matches q s
  | p ∨ q => matches p s \/ matches q s
  | p → q => matches p s -> matches q s

  | X p =>
    match s with
    | []      => term
    | _ :: xs => matches p xs
    end

  | p U q =>
    let fix go s :=
        match s with
        | []      => term
        | x :: xs => matches q (x :: xs) \/ (matches p (x :: xs) /\ go xs)
        end in go s

  | ◇ p =>
    let fix go s :=
        match s with
        | []      => term
        | x :: xs => matches p (x :: xs) \/ go xs
        end in go s

  | □ p =>
    let fix go s :=
        match s with
        | []      => True
        | x :: xs => matches p (x :: xs) /\ go xs
        end in go s
  end.

Lemma matches_bottom T :
  matches (⊥) T <-> False.
Proof. simpl; intuition auto. Qed.

Lemma matches_not L T :
  matches (¬ L) T <-> ~ matches L T.
Proof. simpl; intuition auto. Qed.

Lemma matches_contradiction L T :
  matches L T -> matches (¬ L) T -> False.
Proof. simpl; intuition auto. Qed.

Lemma matches_and L1 L2 T :
  matches (L1 ∧ L2) T <-> matches L1 T /\ matches L2 T.
Proof. simpl; intuition auto. Qed.

Lemma matches_or L1 L2 T :
  matches (L1 ∨ L2) T <-> matches L1 T \/ matches L2 T.
Proof. simpl; intuition auto. Qed.

Lemma matches_impl L1 L2 T :
  matches (L1 → L2) T <-> (matches L1 T -> matches L2 T).
Proof. simpl; intuition auto. Qed.

Lemma matches_next L T x :
  matches (X L) (x :: T) <-> matches L T.
Proof. simpl; intuition auto. Qed.

Lemma matches_eventually L T x :
  matches (◇ L) (x :: T) <-> matches L (x :: T) \/ matches (◇ L) T.
Proof. simpl; intuition auto. Qed.

Lemma matches_until L1 L2 T x :
  matches (L1 U L2) (x :: T) <->
  matches L2 (x :: T) \/
    (matches L1 (x :: T) /\ matches (L1 U L2) T).
Proof. simpl; intuition auto. Qed.

Lemma matches_always L T x :
  matches (□ L) (x :: T) <-> matches L (x :: T) /\ matches (□ L) T.
Proof. simpl; intuition auto. Qed.

Definition impl (φ ψ : LTL) := ¬φ ∨ ψ.

Definition iff (φ ψ : LTL) := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := iff (at level 50).

(* (ψ remains true until and including once φ becomes true.
   If φ never become true, ψ must remain true forever.) *)
Definition release (φ ψ : LTL) := ¬(¬φ U ¬ψ).
Notation "p 'R' q" := (release p q) (at level 50).

Definition weakUntil (φ ψ : LTL) := (φ U ψ) ∨ □ φ.
Notation "p 'W' q" := (weakUntil p q) (at level 50).

Definition strongRelease (φ ψ : LTL) := ψ U (φ ∧ ψ).
Notation "p 'M' q" := (strongRelease p q) (at level 50).

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

Infix "≈" := equiv (at level 70).

Ltac ltl_prep :=
  split;
  repeat intro;
  repeat unfold In, release, weakUntil, strongRelease in *;
  match goal with
  | [ T : Stream |- _ ] => induction T
  | [ T : list a |- _ ] => induction T
  end;
  simpl in *;
  intuition auto;
  try discriminate;
  repeat match goal with
  | [ H : (_ -> False) -> False |- _ ] => apply NNPP in H
  | [ H : ?P |- ?P \/ _ ] => left
  | [ H : ?P |- _ \/ ?P ] => right
  | _ => idtac
  end.

Ltac ltl :=
  ltl_prep;
  auto;
  intuition.

(* These properties are proven to hold in up to three conditions:

   ≈ (Weak)
     The property holds, even if early terminate of the finite input causes a
     match to be incomplete. For example, a proposition against an empty
     input.

   ≈[strong]
     The property holds only if it matches some infix of the finite input
     exactly. Partial matches are not allowed.

   ≈[infinite]
     The property holds only against infinite inputs. *)

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof. ltl. Qed.

(* ψ always remains true *)
Lemma always_remains (ψ : LTL) : □ ψ ≈[strong] ⊥ R ψ.
Proof. ltl. Qed.

Lemma always_not_eventually (ψ : LTL) : □ ψ ≈[strong] ¬◇ ¬ψ.
Proof. ltl. Qed.

Lemma weakUntil_until (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Proof. ltl. Qed.

Lemma weakUntil_release (φ ψ : LTL) : φ W ψ ≈[infinite] ψ R (ψ ∨ φ).
Proof. ltl. Qed.

Lemma until_eventually_or (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof. ltl. Qed.

Lemma release_weakUntil (φ ψ : LTL) : φ R ψ ≈[infinite] ψ W (ψ ∧ φ).
Proof. ltl_prep; inversion H; intuition. Qed.

Lemma strongRelease_not_weakUntil (φ ψ : LTL) : φ M ψ ≈[infinite] ¬(¬φ W ¬ψ).
Proof. ltl_prep; inversion H; intuition. Qed.

Lemma strongRelease_release_or (φ ψ : LTL) : φ M ψ ≈[infinite] (φ R ψ) ∧ ◇ φ.
Proof. ltl_prep; inversion H; intuition. Qed.

Lemma strongRelease_release (φ ψ : LTL) : φ M ψ ≈[infinite] φ R (ψ ∧ ◇ φ).
Proof. ltl. Qed.

(** Distributivity *)

Lemma next_or (φ ψ : LTL) : X (φ ∨ ψ) ≈ (X φ) ∨ (X ψ).
Proof. ltl. Qed.

Lemma next_and (φ ψ : LTL) : X (φ ∧ ψ) ≈ (X φ) ∧ (X ψ).
Proof. ltl. Qed.

Lemma next_until (φ ψ : LTL) : X (φ U ψ) ≈[infinite] (X φ) U (X ψ).
Proof. ltl. Qed.

Lemma eventually_or (φ ψ : LTL) : ◇ (φ ∨ ψ) ≈ (◇ φ) ∨ (◇ ψ).
Proof. ltl. Qed.

Lemma always_and (φ ψ : LTL) : □ (φ ∧ ψ) ≈ (□ φ) ∧ (□ ψ).
Proof. ltl. Qed.

Lemma until_or (ρ φ ψ : LTL) : ρ U (φ ∨ ψ) ≈ (ρ U φ) ∨ (ρ U ψ).
Proof. ltl. Qed.

Lemma and_until (ρ φ ψ : LTL) : (φ ∧ ψ) U ρ ≈ (φ U ρ) ∧ (ψ U ρ).
Proof. ltl. Qed.

(** Negation propagation *)

Lemma not_next (φ : LTL) : ¬(X φ) ≈[infinite] X ¬φ.
Proof. ltl. Qed.

Lemma not_eventually (φ : LTL) : ¬(◇ φ) ≈[strong] □ ¬φ.
Proof. ltl. Qed.

Lemma not_until (φ ψ : LTL) : ¬ (φ U ψ) ≈ (¬φ R ¬ψ).
Proof. ltl. Qed.

Lemma not_weakUntil (φ ψ : LTL) : ¬ (φ W ψ) ≈[infinite] (¬φ M ¬ψ).
Proof. ltl. Qed.

Lemma not_always (φ : LTL) : ¬(□ φ) ≈[infinite] ◇ ¬φ.
Proof. ltl. Qed.

Lemma not_release (φ ψ : LTL) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Proof. ltl. Qed.

Lemma not_strongRelease (φ ψ : LTL) : ¬ (φ M ψ) ≈[infinite] (¬φ W ¬ψ).
Proof. ltl. Qed.

(** Special Temporal properties *)

Lemma not_not_eventually (φ : LTL) : ◇ ◇ φ ≈ ◇ φ.
Proof. ltl. Qed.

Lemma not_not_always (φ : LTL) : □ □ φ ≈ □ φ.
Proof. ltl. Qed.

Lemma until_until (φ ψ : LTL) : φ U (φ U ψ) ≈ φ U ψ.
Proof. ltl. Qed.

Lemma or_and_next_until (φ ψ : LTL) : ψ ∨ (φ ∧ X(φ U ψ)) ≈[infinite] φ U ψ.
Proof. ltl. Qed.

Lemma or_and_next_weakUntil (φ ψ : LTL) : ψ ∨ (φ ∧ X(φ W ψ)) ≈[infinite] φ W ψ.
Proof. ltl. Qed.

Lemma and_or_next_release (φ ψ : LTL) : ψ ∧ (φ ∨ X(φ R ψ)) ≈[infinite] φ R ψ.
Proof. ltl. Qed.

Lemma or_next_always (φ : LTL) : φ ∧ X(□ φ) ≈[infinite] □ φ.
Proof. ltl. Qed.

Lemma or_next_eventually (φ : LTL) : φ ∨ X(◇ φ) ≈ ◇ φ.
Proof. ltl. Qed.

End LTL.
