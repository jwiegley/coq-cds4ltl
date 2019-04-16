Require Import
  Program
  Coq.Lists.List
  Coq.Relations.Relation_Definitions
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Logic.Classical
  Coq.omega.Omega
  Coq.Sets.Ensembles
  Hask.Prelude
  Hask.Control.Monad
  Hask.Data.Maybe.

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

Definition Stream := list a.

Inductive LTL : Type :=
  (* Boolean layer *)
  | Top
  | Bottom

  | Accept (v : a -> LTL)
  | Reject (v : a -> LTL)

  | Not   (p : LTL)

  | And   (p q : LTL)
  | Or    (p q : LTL)

  (* Temporal layer *)
  | Next       (p : LTL)

  | Until      (p q : LTL)
  | Release    (p q : LTL)

  (* Having these extra constructors allows us to prove certain of the LTL
     rules without requiring the assumption of infinite streams. *)
  | Eventually (p : LTL)
  | Always     (p : LTL).

Notation "⊤"       := Top                (at level 45).
Notation "⊥"       := Bottom             (at level 45).
Notation "¬ x"     := (Not x)            (at level 0).
Infix    "∧"       := And                (at level 45).
Infix    "∨"       := Or                 (at level 45).
Notation "p → q"   := (¬ p ∨ (p ∧ q))    (at level 45).
Notation "'X' x"   := (Next x)           (at level 0).
Notation "p 'U' q" := (Until p q)        (at level 45).
Notation "p 'R' q" := (Release p q)      (at level 45).
Notation "◇ x"     := (Eventually x)     (at level 0).
Notation "□ x"     := (Always x)         (at level 0).

Fixpoint LTL_size (p : LTL) : nat :=
  match p with
  | Accept v     => 1
  | Reject v     => 1
  | Top          => 1
  | Bottom       => 1
  | Not p        => 1 + LTL_size p
  | And p q      => 1 + LTL_size p + LTL_size q
  | Or p q       => 1 + LTL_size p + LTL_size q
  | Next p       => 1 + LTL_size p
  | Until p q    => 1 + LTL_size p + LTL_size q
  | Release p q  => 1 + LTL_size p + LTL_size q
  | Eventually p => 1 + LTL_size p
  | Always p     => 1 + LTL_size p
  end.

(* [term] is a type that is found at the end of a partial trace match. By
   choosing [False], one can express that formula must exactly match within a
   trace. *)
Variable term : Prop.

Fixpoint matches (l : LTL) (s : Stream) {struct l} : Prop :=
  match l with
  | ⊤       => True
  | ⊥       => False

  | Accept v => match s with
                | []     => term
                | x :: _ => matches (v x) s
                end
  | Reject v => match s with
                | []     => term
                | x :: _ => ~ matches (v x) s
                end

  | ¬ p     => ~ matches p s

  | p ∧ q   => matches p s /\ matches q s
  | p ∨ q   => matches p s \/ matches q s

  | X p     => match s with
               | []      => term
               | _ :: xs => matches p xs
               end

  | p U q   => let fix go s :=
                   match s with
                   | []      => term
                   | _ :: xs => matches q s \/ (matches p s /\ go xs)
                   end in go s

  | p R q   => let fix go s :=
                   match s with
                   | []      => term
                   | _ :: xs => matches q s /\ (matches p s \/ go xs)
                   end in go s

  | ◇ p     => let fix go s :=
                   match s with
                   | []      => term
                   | _ :: xs => matches p s \/ go xs
                   end in go s

  | □ p     => let fix go s :=
                   match s with
                   | []      => True
                   | _ :: xs => matches p s /\ go xs
                   end in go s
  end.

Fixpoint pnf (l : LTL) : LTL :=
  match l with
  | ⊤        => l
  | ⊥        => l
  | Accept v => l
  | Reject v => l
  | ¬ p      => negate p
  | p ∧ q    => pnf p ∧ pnf q
  | p ∨ q    => pnf p ∨ pnf q
  | X p      => X (pnf p)
  | p U q    => pnf p U pnf q
  | p R q    => pnf p R pnf q
  | ◇ p      => ◇ (pnf p)
  | □ p      => □ (pnf p)
  end

with negate (l : LTL) : LTL :=
  match l with
  | ⊤         => ⊥
  | ⊥         => ⊤
  | Accept v  => Reject v
  | Reject v  => Accept v
  | ¬ p       => pnf p
  | p ∧ q     => negate p ∨ negate q
  | p ∨ q     => negate p ∧ negate q
  | X p       => X (negate p)
  | p U q     => negate p R negate q
  | p R q     => negate p U negate q
  | ◇ p       => □ (negate p)
  | □ p       => ◇ (negate p)
  end.

Fixpoint positive (l : LTL) : Prop :=
  match l with
  | ⊤        => True
  | ⊥        => True
  | Accept v => True
  | Reject v => True
  | ¬ _      => False
  | p ∧ q    => positive p /\ positive q
  | p ∨ q    => positive p /\ positive q
  | X p      => positive p
  | p U q    => positive p /\ positive q
  | p R q    => positive p /\ positive q
  | ◇ p      => positive p
  | □ p      => positive p
  end.

Lemma pnf_complete (l : LTL) : positive (pnf l).
Proof. induction l; simpl in *; intuition auto. Qed.

Local Hint Resolve negate_complete.

Fixpoint pnf (l : LTL) : LTL :=
  match l with
  | ⊤        => l
  | ⊥        => l
  | Accept v => l
  | Reject v => l
  | ¬ p      => negate p
  | p ∧ q    => pnf p ∧ pnf q
  | p ∨ q    => pnf p ∨ pnf q
  | X p      => X (pnf p)
  | p U q    => pnf p U pnf q
  | p R q    => pnf p R pnf q
  | ◇ p      => ◇ (pnf p)
  | □ p      => □ (pnf p)
  end.

Lemma pnf_complete (l : LTL) : positive (pnf l).
Proof. induction l; simpl in *; intuition auto. Qed.

Fixpoint expand (l : LTL) : LTL :=
  match l with
  | ⊤        => l
  | ⊥        => l
  | Accept v => l
  | Reject v => l
  | ¬ p      => ¬ (expand p)
  | p ∧ q    => expand p ∧ expand q
  | p ∨ q    => expand p ∨ expand q
  | X p      => X (expand p)
  | p U q    => expand q ∨ (expand p ∧ X (p U q))
  | p R q    => expand q ∨ (expand p ∧ X (p U q))
  | ◇ p      => expand p ∨ X (◇ p)
  | □ p      => expand p ∧ X (□ p)
  end.

Fixpoint shallow (l : LTL) : Prop :=
  match l with
  | ⊤        => True
  | ⊥        => True
  | Accept v => True
  | Reject v => True
  | ¬ p      => shallow p
  | p ∧ q    => shallow p /\ shallow q
  | p ∨ q    => shallow p /\ shallow q
  | X p      => True
  | p U q    => False
  | p R q    => False
  | ◇ p      => False
  | □ p      => False
  end.

Lemma expand_complete (l : LTL) : shallow (expand l).
Proof. induction l; simpl in *; intuition auto. Qed.

(*
Fixpoint normal_size (l : LTL) : option nat :=
  match l with
  | ⊤        => Some 0
  | ⊥        => Some 0
  | Accept v => Some 1
  | Reject v => Some 1
  | ¬ p      => normal_size p
  | p ∧ q    => liftA2 max (normal_size p) (normal_size q)
  | p ∨ q    => liftA2 min (normal_size p) (normal_size q)
  | X p      => liftA2 plus (Some 1) (normal_size p)
  | p U q    => 1 + normal_size p + normal_size q
  | p R q    => 1 + normal_size p + normal_size q
  | ◇ p      => 1 + normal_size p
  | □ p      => 1 + normal_size p
  end.

Fixpoint fuel_needed (l : LTL) : option nat :=
  match l with
  | ⊤        => Some 0
  | ⊥        => Some 0
  | Accept v => Some 1
  | Reject v => Some 1
  | ¬ p      => fuel_needed p
  | p ∧ q    => liftA2 max (fuel_needed p) (fuel_needed q)
  | p ∨ q    => liftA2 min (fuel_needed p) (fuel_needed q)
  | X p      => liftA2 plus (Some 1) (fuel_needed p)
  | p U q    => fuel_needed q
  | p R q    => fuel_needed q
  | ◇ p      => fuel_needed p
  | □ p      => None
  end.

Ltac fromJust :=
  match goal with
    [ H : Just _ = Just _ |- _ ] =>
    inversion H; subst; clear H
  end.

Lemma fuel_needed_by_expand l : forall n m,
  fuel_needed (expand l) = Some n ->
  fuel_needed l = Some m ->
  n <= m.
Proof.
  induction l; simpl in *; intros;
  unfold Maybe_map, Maybe_apply in *;
  repeat fromJust;
  try destruct (fuel_needed (expand l1)) eqn:?;
  try destruct (fuel_needed (expand l2)) eqn:?;
  try destruct (fuel_needed l1) eqn:?;
  try destruct (fuel_needed l2) eqn:?;
  repeat fromJust;
  try discriminate; auto;
  try apply Nat.max_le_compat; auto;
  try apply Nat.min_le_compat; auto.
  - destruct (fuel_needed (expand l)) eqn:?;
    destruct (fuel_needed l) eqn:?;
    try discriminate;
    repeat fromJust.
    apply le_n_S.
    now apply IHl.
  - now apply Nat.min_le_iff; auto.
  - now apply Nat.min_le_iff; auto.
  - now apply Nat.min_le_iff; auto.
  - now apply Nat.min_le_iff; auto.
  - destruct (fuel_needed (expand l)) eqn:?;
    destruct (fuel_needed l) eqn:?;
    try discriminate;
    repeat fromJust.
    now apply Nat.min_le_iff; auto.
Qed.

Lemma expand_always_needs_fuel :
  forall n, fuel_needed l = Some n <-> fuel_needed (expand l) = Some m
    else fuel_needed (expand l) = None.
Proof.
  induction l; simpl in *; intros;
  unfold Maybe_map, Maybe_apply in *;
  try destruct IHl;
  try destruct IHl1;
  try destruct IHl2;
  try destruct (fuel_needed (expand l1)) eqn:?;
  try destruct (fuel_needed (expand l2)) eqn:?;
  try destruct (fuel_needed (expand l)) eqn:?;
  try destruct (fuel_needed l1) eqn:?;
  try destruct (fuel_needed l2) eqn:?;
  try destruct (fuel_needed l) eqn:?;
  try (now eexists; eauto);
  try rewrite H;
  try rewrite H0;
  try (now eexists; eauto);
  try destruct H, H, H0;
  try first [ left; split; eauto | right; split; eauto ];
  try (now eexists; eauto).

Lemma expand_always_needs_fuel :
  forall l,
    IF exists n, fuel_needed l = Some n
    then exists m, fuel_needed (expand l) = Some m
    else fuel_needed (expand l) = None.
Proof.
  induction l; simpl in *; intros;
  unfold Maybe_map, Maybe_apply in *;
  try destruct IHl;
  try destruct IHl1;
  try destruct IHl2;
  try destruct (fuel_needed (expand l1)) eqn:?;
  try destruct (fuel_needed (expand l2)) eqn:?;
  try destruct (fuel_needed (expand l)) eqn:?;
  try destruct (fuel_needed l1) eqn:?;
  try destruct (fuel_needed l2) eqn:?;
  try destruct (fuel_needed l) eqn:?;
  try (now eexists; eauto);
  try rewrite H;
  try rewrite H0;
  try (now eexists; eauto);
  try destruct H, H, H0;
  try first [ left; split; eauto | right; split; eauto ];
  try (now eexists; eauto).
  left; split.
*)

Fixpoint prune (l : LTL) : LTL :=
  match l with
  | ⊤        => l
  | ⊥        => l
  | Accept v => l
  | Reject v => l
  | ¬ p      => match prune p with
                | ¬ p => p
                | p   => ¬ p
                end
  | p ∧ q    => match prune p with
                | ⊤ => prune q
                | p => match prune q with
                       | ⊤ => p
                       | q => p ∧ q
                       end
                end
  | p ∨ q    => match prune p with
                | ⊥ => prune q
                | p => match prune q with
                       | ⊥ => p
                       | q => p ∨ q
                       end
                end
  | X p      => X (prune p)
  | p U q    => prune p U prune q
  | p R q    => prune p R prune q
  | ◇ p      => ◇ (prune p)
  | □ p      => □ (prune p)
  end.

Definition iff (φ ψ : LTL) := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := iff (at level 45).

(* (ψ remains true until and including once φ becomes true.
   If φ never become true, ψ must remain true forever.) *)
Definition weakUntil (φ ψ : LTL) := (φ U ψ) ∨ □ φ.
Notation "p 'W' q" := (weakUntil p q) (at level 45).

Definition strongRelease (φ ψ : LTL) := ψ U (φ ∧ ψ).
Notation "p 'M' q" := (strongRelease p q) (at level 45).

Definition ltl_weak_equiv (p q : LTL) : Prop :=
  term -> matches p ≈ matches q.
Arguments ltl_weak_equiv p q /.

Infix "≈[weak]" := ltl_weak_equiv (at level 70).

Definition ltl_strong_equiv (p q : LTL) : Prop :=
  (term -> False) -> matches p ≈ matches q.
Arguments ltl_strong_equiv p q /.

Infix "≈[strong]" := ltl_strong_equiv (at level 70).

Definition ltl_infinite_equiv (p q : LTL) : Prop :=
  forall T : Stream, length T > 0 -> matches p T <-> matches q T.
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

(* Infix "≈" := equiv (at level 70). *)

Ltac ltl_prep :=
  split;
  repeat intro;
  repeat unfold In, weakUntil, strongRelease in *;
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

Ltac ltl := ltl_prep; auto; intuition; try (inversion H; intuition).

(* These properties are proven to hold in up to three conditions:

   ≈ (Weak) The property holds, even if early termination of a finite input
     causes the match to be incomplete. For example, a proposition against an
     empty input.

   ≈[strong] The property holds only if it matches some infix of the finite
     input exactly. Partial matches are not allowed.

   ≈[infinite] The property holds only against infinite inputs. *)

Lemma negate_correct l : l ≈ negate (¬ l).
Proof.
  ltl_prep.
  induction l; simpl in *; auto.

Lemma negate_correct l : ¬ l ≈ negate l.
Proof.
  unfold negate.
  ltl_prep.
Qed.

Lemma pnf_correct l : l ≈ pnf l.
Proof. ltl. Qed.

Lemma expand_correct l : l ≈ expand l.
Proof. ltl. Qed.

Lemma prune_correct l : l ≈ prune l.
Proof. ltl. Qed.

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof. ltl. Qed.

(* ψ always remains true *)
Lemma always_remains (ψ : LTL) : □ ψ ≈ ⊥ R ψ.
Proof. ltl. Qed.

Lemma always_not_eventually (ψ : LTL) : □ ψ ≈[strong] ¬◇ ¬ψ.
Proof. ltl. Qed.

Lemma weakUntil_until (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Proof. ltl. Qed.

Lemma weakUntil_release (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Proof. ltl. Qed.

Lemma until_eventually_or (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof. ltl. Qed.

Lemma release_weakUntil (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Proof. ltl. Qed.

Lemma release_until (φ ψ : LTL) : φ R ψ ≈ ¬(¬φ U ¬ψ).
Proof. ltl. Qed.

Lemma strongRelease_not_weakUntil (φ ψ : LTL) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Proof. ltl. Qed.

Lemma strongRelease_release_or (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Proof. ltl. Qed.

Lemma strongRelease_release (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Proof. ltl. Qed.

(** Distributivity *)

Lemma next_or (φ ψ : LTL) : X (φ ∨ ψ) ≈ (X φ) ∨ (X ψ).
Proof. ltl. Qed.

Lemma next_and (φ ψ : LTL) : X (φ ∧ ψ) ≈ (X φ) ∧ (X ψ).
Proof. ltl. Qed.

Lemma next_until (φ ψ : LTL) : X (φ U ψ) ≈ (X φ) U (X ψ).
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

Lemma not_next (φ : LTL) : ¬(X φ) ≈ X ¬φ.
Proof. ltl. Qed.

Lemma not_eventually (φ : LTL) : ¬(◇ φ) ≈[strong] □ ¬φ.
Proof. ltl. Qed.

Lemma not_until (φ ψ : LTL) : ¬ (φ U ψ) ≈ (¬φ R ¬ψ).
Proof. ltl. Qed.

Lemma not_weakUntil (φ ψ : LTL) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Proof. ltl. Qed.

Lemma not_always (φ : LTL) : ¬(□ φ) ≈ ◇ ¬φ.
Proof. ltl. Qed.

Lemma not_release (φ ψ : LTL) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Proof. ltl. Qed.

Lemma not_strongRelease (φ ψ : LTL) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Proof. ltl. Qed.

(** Absorption laws *)

Lemma asborb_eventually (φ : LTL) : ◇ □ ◇ φ ≈ □ ◇ φ.
Proof. ltl. Qed.

Lemma asborb_always (φ : LTL) : □ ◇ □ φ ≈ ◇ □ φ.
Proof. ltl. Qed.

(** Special Temporal properties *)

Lemma eventually_idempotent (φ : LTL) : ◇ ◇ φ ≈ ◇ φ.
Proof. ltl. Qed.

Lemma always_idempotent (φ : LTL) : □ □ φ ≈ □ φ.
Proof. ltl. Qed.

Lemma until_idempotent_left  (φ ψ : LTL) : (φ U ψ) U ψ ≈ φ U ψ.
Proof. ltl. Qed.

Lemma until_idempotent_right (φ ψ : LTL) : φ U (φ U ψ) ≈ φ U ψ.
Proof. ltl. Qed.

(** Expansion laws *)

Lemma expand_until      (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ X(φ U ψ)).
Proof. ltl. Qed.

Lemma expand_weakUntil  (φ ψ : LTL) : φ W ψ ≈ ψ ∨ (φ ∧ X(φ W ψ)).
Proof. ltl. Qed.

Lemma expand_release    (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ X(φ R ψ)).
Proof. ltl. Qed.

Lemma expand_always     (φ : LTL)   :   □ φ ≈ φ ∧ X(□ φ).
Proof. ltl. Qed.

Lemma expand_eventually (φ : LTL)   :   ◇ φ ≈ φ ∨ X(◇ φ).
Proof. ltl. Qed.

End LTL.

Arguments Top {a}.
Arguments Bottom {a}.
Arguments Accept {a} v.
Arguments Reject {a} v.
Arguments Not {a} p.
Arguments And {a}.
Arguments Or {a}.
Arguments Next {a} p.
Arguments Until {a} p q.
Arguments Release {a} p q.
Arguments Eventually {a} p.
Arguments Always {a} p.

Arguments weakUntil {a} φ ψ.
Arguments strongRelease {a} φ ψ.

Bind Scope ltl_scope with LTL.
Delimit Scope ltl_scope with LTL.

Notation "⊤"       := Top                 (at level 45) : ltl_scope.
Notation "⊥"       := Bottom              (at level 45) : ltl_scope.
Notation "¬ x"     := (Not x)             (at level 0)  : ltl_scope.
Infix    "∧"       := And                 (at level 45) : ltl_scope.
Infix    "∨"       := Or                  (at level 45) : ltl_scope.
Notation "p → q"   := (¬ p ∨ (p ∧ q))%LTL (at level 45) : ltl_scope.
Notation "'X' x"   := (Next x)            (at level 0)  : ltl_scope.
Notation "p 'U' q" := (Until p q)         (at level 45) : ltl_scope.
Notation "p 'R' q" := (Release p q)       (at level 45) : ltl_scope.
Notation "◇ x"     := (Eventually x)      (at level 0)  : ltl_scope.
Notation "□ x"     := (Always x)          (at level 0)  : ltl_scope.
Notation "p 'W' q" := (weakUntil p q)     (at level 45) : ltl_scope.
Notation "p 'M' q" := (strongRelease p q) (at level 45) : ltl_scope.

Definition ifThen `(p : a -> bool) (f : a -> LTL a) :=
  Accept (fun x => if p x then f x else ⊤)%LTL.

Definition series {a} :=
  fold_right (fun x rest => x ∧ @Next a rest)%LTL (⊤)%LTL.

Section Examples.

Open Scope ltl_scope.

Definition num (n : nat) := Accept (fun x => if x =? n then ⊤ else ⊥).

Example ex_match_query :
  matches nat False (num 1 ∧ (X (num 2)))
          [1; 2].
Proof. simpl; auto. Qed.

Example ex_match_series :
  matches nat False (series [num 1; num 2])
          [1; 2].
Proof. simpl; auto. Qed.

Example ex_match_sample1 :
  matches nat False (□ (num 3 → ◇ (num 8)))
          [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. simpl; intuition auto. Qed.

Example ex_match_sample2 :
  matches nat False (□ (ifThen (fun n => n =? 3)
                               (fun n => ◇ (num (n + 5)))))
          [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. simpl; intuition auto. Qed.

End Examples.
