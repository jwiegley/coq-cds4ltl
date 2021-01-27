Require Import
  Program
  FunInd
  Coq.Lists.List
  Coq.Relations.Relation_Definitions
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Logic.Classical.

Open Scope program_scope.
Open Scope list_scope.

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

  | And   (p q : LTL)
  | Or    (p q : LTL)

  (* Temporal layer *)
  | Next       (p : LTL)

  | Until      (p q : LTL)
  | Release    (p q : LTL).

Notation "⊤"       := Top                (at level 45).
Notation "⊥"       := Bottom             (at level 45).
Infix    "∧"       := And                (at level 45).
Infix    "∨"       := Or                 (at level 45).
Notation "'X' x"   := (Next x)           (at level 0).
Notation "p 'U' q" := (Until p q)        (at level 45).
Notation "p 'R' q" := (Release p q)      (at level 45).
Notation "◇ x"     := (⊤ U x)            (at level 0).
Notation "□ x"     := (⊥ R x)            (at level 0).


Fixpoint LTL_size (p : LTL) : nat :=
  match p with
  | Top          => 1
  | Bottom       => 1
  | Accept v     => 1
  | And p q      => 1 + LTL_size p + LTL_size q
  | Or p q       => 1 + LTL_size p + LTL_size q
  | Next p       => 1 + LTL_size p
  | Until p q    => 1 + LTL_size p + LTL_size q
  | Release p q  => 1 + LTL_size p + LTL_size q
  end.

Fixpoint matches (l : LTL) (s : Stream) {struct l} : Prop :=
  match l with
  | ⊤ => True
  | ⊥ => False

  | Accept v =>
    match s with
    | []      => True
    | x :: xs => matches (v x) s
    end

  | p ∧ q => matches p s /\ matches q s
  | p ∨ q => matches p s \/ matches q s

  | X p =>
    match s with
    | []      => matches p []
    | x :: xs => matches p xs
    end

  | p U q =>
    let fix go s :=
        match s with
        | [] => matches q s
        | _ :: xs => matches q s \/ (matches p s /\ go xs)
        end in go s

  | p R q =>
    let fix go s :=
        match s with
        | [] => matches q s
        | _ :: xs => matches q s /\ (matches p s \/ go xs)
        end in go s
  end.

Function negate (l : LTL) : LTL :=
  match l with
  | ⊤        => ⊥
  | ⊥        => ⊤
  | Accept v => Accept (negate ∘ v)
  | p ∧ q    => negate p ∨ negate q
  | p ∨ q    => negate p ∧ negate q
  | X p      => X (negate p)
  | p U q    => negate p R negate q
  | p R q    => negate p U negate q
  end.

Notation "¬ x"     := (negate x)         (at level 0).
Notation "p → q"   := (¬ p ∨ (p ∧ q))    (at level 45).

Definition iff (φ ψ : LTL) := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := iff (at level 45).

(* (ψ remains true until and including once φ becomes true.
   If φ never become true, ψ must remain true forever.) *)
Definition weakUntil (φ ψ : LTL) := (φ U ψ) ∨ □ φ.
Notation "p 'W' q" := (weakUntil p q) (at level 45).

Definition strongRelease (φ ψ : LTL) := (φ R ψ) ∧ ◇ φ.
Notation "p 'M' q" := (strongRelease p q) (at level 45).

Fixpoint expand (l : LTL) : LTL :=
  match l with
  | ⊤        => l
  | ⊥        => l
  | Accept v => Accept (expand ∘ v)
  | p ∧ q    => expand p ∧ expand q
  | p ∨ q    => expand p ∨ expand q
  | X p      => X (expand p)
  | p U q    => expand q ∨ (expand p ∧ X (p U q))
  | p R q    => expand q ∧ (expand p ∨ X (p R q))
  end.

Definition not_complex (l : LTL) : Prop :=
  match l with
  | p U q => False
  | p R q => False
  | _     => True
  end.

Lemma not_complex_expand : forall l, not_complex (expand l).
Proof. induction l; simpl; auto. Qed.

Fixpoint shallow (l : LTL) : Prop :=
  match l with
  | ⊤        => True
  | ⊥        => True
  | Accept v => True
  | p ∧ q    => shallow p /\ shallow q
  | p ∨ q    => shallow p /\ shallow q
  | X p      => True
  | p U q    => False
  | p R q    => False
  end.

Lemma expand_complete (l : LTL) : shallow (expand l).
Proof. induction l; simpl in *; intuition auto. Qed.

Function prune (l : LTL) : LTL :=
  match l with
  | ⊤        => l
  | ⊥        => l
  | Accept v => l
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
  end.

Definition ltl_equiv (p q : LTL) : Prop :=
  forall T, matches p T <-> matches q T.
Arguments ltl_equiv p q /.

Global Program Instance Equivalence_ltl_equiv : Equivalence ltl_equiv.
Next Obligation.
  unfold ltl_equiv.
  repeat intro; auto.
  reflexivity.
Qed.
Next Obligation.
  unfold ltl_equiv.
  repeat intro; intuition.
Qed.
Next Obligation.
  unfold ltl_equiv.
  repeat intro; firstorder.
Qed.

Global Program Instance Accept_Proper :
  Proper ((eq ==> ltl_equiv) ==> ltl_equiv) Accept.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  destruct T; intuition;
  constructor.
Qed.

Global Program Instance And_Proper :
  Proper (ltl_equiv ==> ltl_equiv ==> ltl_equiv) And.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  destruct T; intuition;
  constructor.
Qed.

Global Program Instance Or_Proper :
  Proper (ltl_equiv ==> ltl_equiv ==> ltl_equiv) Or.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  destruct T; intuition;
  constructor.
Qed.

Global Program Instance Next_Proper :
  Proper (ltl_equiv ==> ltl_equiv) Next.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  destruct T; firstorder;
  constructor.
Qed.

Global Program Instance Until_Proper :
  Proper (ltl_equiv ==> ltl_equiv ==> ltl_equiv) Until.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  induction T; intuition;
  constructor.
Qed.

Global Program Instance Release_Proper :
  Proper (ltl_equiv ==> ltl_equiv ==> ltl_equiv) Release.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  induction T; intuition;
  constructor.
Qed.

Global Program Instance matches_Proper :
  Proper (ltl_equiv ==> eq ==> equiv) matches.
Next Obligation.
  repeat intro; subst.
  apply H; intros.
Qed.

Infix "≈" := equiv (at level 48).

Lemma not_not (φ : LTL) : ¬¬ φ ≈ φ.
Proof.
  induction φ; simpl; intuition;
  try (now rewrite IHφ1, IHφ2);
  try (now rewrite IHφ).
  apply Accept_Proper; repeat intro.
  subst.
  apply H.
Qed.

Ltac ltl :=
  split;
  repeat intro;
  repeat unfold weakUntil, strongRelease in *;
  match goal with
  | [ T : Stream |- _ ] => induction T
  | [ T : list a |- _ ] => induction T
  end;
  simpl in *;
  intuition auto;
  try discriminate;
  repeat match goal with
  | [ H : (_ -> False) -> False |- _ ] => apply NNPP in H
  | [ H : ?P |- ?P \/ _ ] => now left
  | [ H : ?P |- _ \/ ?P ] => now right
  | _ => idtac
  end;
  match goal with
  | [ T : Stream |- _ ] => destruct T; intuition auto
  | [ T : list a |- _ ] => destruct T; intuition auto
  | _ => idtac
  end;
  rewrite ?not_not in * |- *;
  firstorder.

(** Principles of negation *)

Lemma not_and (φ ψ : LTL) : ¬ (φ ∧ ψ) ≈ ¬ φ ∨ ¬ ψ.
Proof. now ltl. Qed.

Lemma not_or (φ ψ : LTL) : ¬ (φ ∨ ψ) ≈ ¬ φ ∧ ¬ ψ.
Proof. now ltl. Qed.

Lemma not_next (φ : LTL) : ¬(X φ) ≈ X ¬φ.
Proof. now ltl. Qed.

Lemma not_until (φ ψ : LTL) : ¬ (φ U ψ) ≈ ¬φ R ¬ψ.
Proof. now ltl. Qed.

Lemma not_release (φ ψ : LTL) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Proof. now ltl. Qed.

Lemma not_eventually (φ : LTL) : ¬(◇ φ) ≈ □ ¬φ.
Proof. now ltl. Qed.

Lemma not_always (φ : LTL) : ¬(□ φ) ≈ ◇ ¬φ.
Proof. now ltl. Qed.

Lemma not_weakUntil (φ ψ : LTL) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Proof. now ltl. Qed.

Lemma not_strongRelease (φ ψ : LTL) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Proof. now ltl. Qed.

(** Boolean equivalences *)

Lemma or_comm (φ ψ : LTL) : φ ∨ ψ ≈ ψ ∨ φ.
Proof. now ltl. Qed.

Lemma or_assoc (φ ψ χ : LTL) : φ ∨ (ψ ∨ χ) ≈ (φ ∨ ψ) ∨ χ.
Proof. now ltl. Qed.

Lemma or_bottom (φ : LTL) : φ ∨ (⊥) ≈ φ.
Proof. now ltl. Qed.

Lemma bottom_or (φ : LTL) : (⊥) ∨ φ ≈ φ.
Proof. now ltl. Qed.

Lemma or_and (φ ψ χ : LTL) : φ ∨ (ψ ∧ χ) ≈ (φ ∨ ψ) ∧ (φ ∨ χ).
Proof. now ltl. Qed.

Lemma and_comm (φ ψ : LTL) : φ ∧ ψ ≈ ψ ∧ φ.
Proof. now ltl. Qed.

Lemma and_assoc (φ ψ χ : LTL) : φ ∧ (ψ ∧ χ) ≈ (φ ∧ ψ) ∧ χ.
Proof. now ltl. Qed.

Lemma and_top (φ : LTL) : φ ∧ (⊤) ≈ φ.
Proof. now ltl. Qed.

Lemma top_and (φ : LTL) : (⊤) ∧ φ ≈ φ.
Proof. now ltl. Qed.

Lemma and_or (φ ψ χ : LTL) : φ ∧ (ψ ∨ χ) ≈ (φ ∧ ψ) ∨ (φ ∧ χ).
Proof. now ltl. Qed.

(** Temporal equivalences *)

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof. now ltl. Qed.

(* ψ always remains true *)
Lemma always_remains (ψ : LTL) : □ ψ ≈ ⊥ R ψ.
Proof. now ltl. Qed.

Lemma always_not_eventually (ψ : LTL) : □ ψ ≈ ¬◇ ¬ψ.
Proof. now ltl. Qed.

Lemma until_eventually_or (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof. now ltl. Qed.

Lemma release_until (φ ψ : LTL) : φ R ψ ≈ ¬(¬φ U ¬ψ).
Proof. now ltl. Qed.

Lemma weakUntil_release (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Proof. now ltl. Qed.

Lemma release_weakUntil (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Proof. now ltl. Qed.

Lemma weakUntil_until (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Proof. now ltl. Qed.

Lemma strongRelease_not_weakUntil (φ ψ : LTL) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Proof. now ltl. Qed.

Lemma strongRelease_release_or (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Proof. now ltl. Qed.

Lemma strongRelease_release (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Proof. now ltl. Qed.

(** Distributivity *)

Lemma next_or (φ ψ : LTL) : X (φ ∨ ψ) ≈ (X φ) ∨ (X ψ).
Proof. now ltl. Qed.

Lemma next_and (φ ψ : LTL) : X (φ ∧ ψ) ≈ (X φ) ∧ (X ψ).
Proof. now ltl. Qed.

Lemma next_until (φ ψ : LTL) : X (φ U ψ) ≈ (X φ) U (X ψ).
Proof. now ltl. Qed.

Lemma next_release (φ ψ : LTL) : X (φ R ψ) ≈ (X φ) R (X ψ).
Proof. now ltl. Qed.

Lemma next_eventually (φ : LTL) : X (◇ φ) ≈ ◇ (X φ).
Proof. now ltl. Qed.

Lemma next_always (φ : LTL) : X (□ φ) ≈ □ (X φ).
Proof. now ltl. Qed.

Lemma eventually_or (φ ψ : LTL) : ◇ (φ ∨ ψ) ≈ (◇ φ) ∨ (◇ ψ).
Proof. now ltl. Qed.

Lemma always_and (φ ψ : LTL) : □ (φ ∧ ψ) ≈ (□ φ) ∧ (□ ψ).
Proof. now ltl. Qed.

Lemma until_or (ρ φ ψ : LTL) : ρ U (φ ∨ ψ) ≈ (ρ U φ) ∨ (ρ U ψ).
Proof. now ltl. Qed.

Lemma and_until (ρ φ ψ : LTL) : (φ ∧ ψ) U ρ ≈ (φ U ρ) ∧ (ψ U ρ).
Proof. now ltl. Qed.

(*
Lemma release_or (ρ φ ψ : LTL) : ρ R (φ ∨ ψ) ≈ (ρ R φ) ∨ (ρ R ψ).
Proof. now ltl. Qed.

Lemma and_release (ρ φ ψ : LTL) : (φ ∧ ψ) R ρ ≈ (φ R ρ) ∧ (ψ R ρ).
Proof. now ltl. Qed.
*)

(** Special Temporal properties *)

Lemma eventually_idempotent (φ : LTL) : ◇ ◇ φ ≈ ◇ φ.
Proof. now ltl. Qed.

Lemma always_idempotent (φ : LTL) : □ □ φ ≈ □ φ.
Proof. now ltl. Qed.

Lemma until_idempotent_left  (φ ψ : LTL) : (φ U ψ) U ψ ≈ φ U ψ.
Proof. now ltl. Qed.

Lemma until_idempotent_right (φ ψ : LTL) : φ U (φ U ψ) ≈ φ U ψ.
Proof. now ltl. Qed.

(** Expansion laws *)

Lemma expand_until (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ X(φ U ψ)).
Proof. now ltl. Qed.

Lemma expand_release (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ X(φ R ψ)).
Proof. now ltl. Qed.

Lemma expand_always (φ : LTL) : □ φ ≈ φ ∧ X(□ φ).
Proof. now ltl. Qed.

Lemma expand_eventually (φ : LTL) : ◇ φ ≈ φ ∨ X(◇ φ).
Proof. now ltl. Qed.

Lemma expand_weakUntil  (φ ψ : LTL) : φ W ψ ≈ ψ ∨ (φ ∧ X(φ W ψ)).
Proof. now ltl. Qed.

(** Absorption laws *)

Lemma asborb_eventually (φ : LTL) : ◇ □ ◇ φ ≈ □ ◇ φ.
Proof. now ltl. Qed.

Lemma asborb_always (φ : LTL) : □ ◇ □ φ ≈ ◇ □ φ.
Proof. now ltl. Qed.

(** Correctness of transformations *)

Lemma expand_correct l : expand l ≈ l.
Proof.
  induction l; simpl; intuition;
  rewrite ?IHl, ?IHl1, ?IHl2; try reflexivity.
  - unfold Basics.compose.
    apply Accept_Proper.
    repeat intro; subst.
    now rewrite H.
  - symmetry; apply expand_until.
  - symmetry; apply expand_release.
Qed.

Lemma prune_correct l : prune l ≈ l.
Proof.
  apply prune_ind; simpl; intros; subst; intuition;
  try rewrite e0 in H;
  try rewrite e1 in H0.
  - now ltl.
  - now ltl.
  - now ltl.
  - rewrite H0, <- H.
    clear.
    now ltl.
  - rewrite H, <- H0.
    clear.
    now ltl.
  - rewrite H, H0.
    reflexivity.
  - rewrite H.
    reflexivity.
  - now rewrite H, H0.
  - now rewrite H, H0.
Qed.

End LTL.

Arguments Top {a}.
Arguments Bottom {a}.
Arguments Accept {a} v.
Arguments And {a}.
Arguments Or {a}.
Arguments Next {a} p.
Arguments Until {a} p q.
Arguments Release {a} p q.

Arguments weakUntil {a} φ ψ.
Arguments strongRelease {a} φ ψ.

Bind Scope ltl_scope with LTL.
Delimit Scope ltl_scope with LTL.

Notation "⊤"       := Top                 (at level 45) : ltl_scope.
Notation "⊥"       := Bottom              (at level 45) : ltl_scope.
Notation "¬ x"     := (negate _ x)        (at level 0)  : ltl_scope.
Infix    "∧"       := And                 (at level 45) : ltl_scope.
Infix    "∨"       := Or                  (at level 45) : ltl_scope.
Notation "p → q"   := (¬ p ∨ (p ∧ q))%LTL (at level 45) : ltl_scope.
Notation "'X' x"   := (Next x)            (at level 0)  : ltl_scope.
Notation "p 'U' q" := (Until p q)         (at level 45) : ltl_scope.
Notation "p 'R' q" := (Release p q)       (at level 45) : ltl_scope.
Notation "◇ x"     := (⊤ U x)%LTL         (at level 0)  : ltl_scope.
Notation "□ x"     := (⊥ R x)%LTL         (at level 0)  : ltl_scope.
Notation "p 'W' q" := (weakUntil p q)     (at level 45) : ltl_scope.
Notation "p 'M' q" := (strongRelease p q) (at level 45) : ltl_scope.

Infix "↔" := iff (at level 45) : ltl_scope.

Definition ifThen `(p : a -> bool) (f : a -> LTL a) :=
  Accept (fun x => if p x then f x else ⊤)%LTL.

Fixpoint series {a} (l : list (LTL a)) : LTL a :=
  match l with
  | nil => ⊤
  | [x] => x
  | x :: xs => x ∧ Next (series xs)
  end.

Section Examples.

Open Scope ltl_scope.

Definition num (n : nat) := Accept (fun x => if x =? n then ⊤ else ⊥).

Example ex_match_query  :
  matches nat (num 1 ∧ (X (num 2))) [1; 2].
Proof. simpl; auto. Qed.

Example ex_match_series :
  matches nat (series [num 1; num 2]) [1; 2].
Proof. simpl; auto. Qed.

Example ex_match_sample1 :
  matches nat (◇ (num 3 → ◇ (num 8))) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. simpl; intuition auto. Qed.

Example ex_match_sample2 :
  matches nat (◇ (ifThen (fun n => n =? 3) (fun n => ◇ (num (n + 5)))))
          [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. simpl; intuition auto. Qed.

End Examples.
