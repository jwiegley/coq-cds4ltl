Require Import
  Program
  FunInd
  Coq.Lists.List
  Coq.Relations.Relation_Definitions
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Logic.Classical
  Coq.omega.Omega
  Hask.Prelude
  Hask.Control.Monad
  Hask.Data.Maybe.

Require Import Equations.Equations.
Require Import Equations.EqDec.

Open Scope program_scope.
Open Scope list_scope.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Section LTL.

Variable a : Type.              (* The type of entries in the trace *)

Inductive Stream := Cons : a -> Stream -> Stream.

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

Fixpoint matches (l : LTL) (s : Stream) {struct l} : Prop :=
  match l with
  | ⊤        => True
  | ⊥        => False

  | Accept v => match s with Cons x _ => matches (v x) s end
  | Reject v => match s with Cons x _ => ~ matches (v x) s end

  | ¬ p      => ~ matches p s

  | p ∧ q    => matches p s /\ matches q s
  | p ∨ q    => matches p s \/ matches q s

  | X p      => match s with Cons _ xs => matches p xs end

  | p U q    =>
    let fix go s :=
        match s with
        | Cons _ xs => matches q s \/ (matches p s /\ go xs)
        end in go s

  | p R q    =>
    let fix go s :=
        match s with
        | Cons _ xs => matches q s /\ (matches p s \/ go xs)
        end in go s

  | ◇ p      =>
    let fix go s :=
        match s with
        | Cons _ xs => matches p s \/ go xs
        end in go s

  | □ p      =>
    let fix go s :=
        match s with
        | Cons _ xs => matches p s /\ go xs
        end in go s
  end.

Function pnf (l : LTL) : LTL :=
  match l with
  | ⊤        => l
  | ⊥        => l
  | Accept v => Accept (pnf ∘ v)
  | Reject v => Reject (pnf ∘ v)
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
  | Accept v  => Reject (pnf ∘ v)
  | Reject v  => Accept (pnf ∘ v)
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

Functional Scheme pnf_ind2 := Induction for pnf Sort Prop
  with negate_ind2 := Induction for negate Sort Prop.

Lemma negate_positive (l : LTL) : positive (negate l).
Proof.
  apply negate_ind2 with (P:=fun _ y : LTL => positive y);
  intros; subst; simpl; auto.
Qed.

Lemma pnf_positive (l : LTL) : positive (pnf l).
Proof.
  apply pnf_ind2 with (P0:=fun _ y : LTL => positive y);
  intros; subst; simpl; auto.
Qed.

Fixpoint expand (l : LTL) : LTL :=
  match l with
  | ⊤        => l
  | ⊥        => l
  | Accept v => Accept (expand ∘ v)
  | Reject v => Reject (expand ∘ v)
  | ¬ p      => ¬ (expand p)
  | p ∧ q    => expand p ∧ expand q
  | p ∨ q    => expand p ∨ expand q
  | X p      => X (expand p)
  | p U q    => expand q ∨ (expand p ∧ X (p U q))
  | p R q    => expand q ∧ (expand p ∨ X (p R q))
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

Function prune (l : LTL) : LTL :=
  match l with
  | ⊤        => l
  | ⊥        => l
  | Accept v => l
  | Reject v => l
  | ¬ p      => match prune p with
                | ¬ p' => p'
                | p    => ¬ p
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

Definition ltl_equiv (p q : LTL) : Prop :=
  forall T, matches p T <-> matches q T.
Arguments ltl_equiv p q /.

Program Instance Equivalence_ltl_equiv : Equivalence ltl_equiv.
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

Program Instance Accept_Proper :
  Proper ((eq ==> ltl_equiv) ==> ltl_equiv) Accept.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  destruct T; intuition.
Qed.

Program Instance Reject_Proper :
  Proper ((eq ==> ltl_equiv) ==> ltl_equiv) Reject.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  destruct T; intuition.
Qed.

Program Instance Not_Proper :
  Proper (ltl_equiv ==> ltl_equiv) Not.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  destruct T; intuition.
Qed.

Program Instance And_Proper :
  Proper (ltl_equiv ==> ltl_equiv ==> ltl_equiv) And.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  destruct T; intuition.
Qed.

Program Instance Or_Proper :
  Proper (ltl_equiv ==> ltl_equiv ==> ltl_equiv) Or.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  destruct T; intuition.
Qed.

Program Instance Next_Proper :
  Proper (ltl_equiv ==> ltl_equiv) Next.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  destruct T; firstorder.
Qed.

Program Instance Until_Proper :
  Proper (ltl_equiv ==> ltl_equiv ==> ltl_equiv) Until.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  induction T; intuition;
  right; destruct T; intuition.
Qed.

Program Instance Release_Proper :
  Proper (ltl_equiv ==> ltl_equiv ==> ltl_equiv) Release.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  induction T; intuition;
  right; destruct T; intuition.
Qed.

Program Instance Eventually_Proper :
  Proper (ltl_equiv ==> ltl_equiv) Eventually.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  induction T; intuition;
  right; destruct T; intuition.
Qed.

Program Instance Always_Proper :
  Proper (ltl_equiv ==> ltl_equiv) Always.
Next Obligation.
  repeat intro; simpl.
  unfold ltl_equiv in *.
  induction T; intuition;
  destruct T; intuition.
Qed.

Program Instance matches_Proper :
  Proper (ltl_equiv ==> eq ==> equiv) (matches).
Next Obligation.
  repeat intro; subst.
  now apply H.
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
  end.

(** Logical equivalences *)

Lemma or_comm (φ ψ : LTL) : φ ∨ ψ ≈ ψ ∨ φ.
Proof. ltl. Qed.

Lemma and_comm (φ ψ : LTL) : φ ∧ ψ ≈ ψ ∧ φ.
Proof. ltl. Qed.

(** Temporal equivalences *)

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof. now ltl. Qed.

(* ψ always remains true *)
Lemma always_remains (ψ : LTL) : □ ψ ≈ ⊥ R ψ.
Proof. now ltl. Qed.

Lemma always_not_eventually (ψ : LTL) : □ ψ ≈ ¬◇ ¬ψ.
Proof. now ltl. Qed.

Lemma weakUntil_until (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Proof. now ltl. Qed.

Lemma weakUntil_release (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Proof. now ltl. Qed.

Lemma until_eventually_or (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof. now ltl. Qed.

Lemma release_weakUntil (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Proof. now ltl. Qed.

Lemma release_until (φ ψ : LTL) : φ R ψ ≈ ¬(¬φ U ¬ψ).
Proof.
  ltl; auto.
  apply imply_to_or in H.
  intuition auto.
  apply NNPP in H1; auto.
Qed.

Lemma strongRelease_not_weakUntil (φ ψ : LTL) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Proof.
  ltl.
  apply imply_to_or in H.
  apply imply_to_or in H0.
  destruct H.
    apply NNPP in H; auto.
  destruct H0.
    apply NNPP in H0; auto.
  intuition auto.
Qed.

Lemma strongRelease_release_or (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Proof. now ltl. Qed.

Lemma strongRelease_release (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Proof. ltl; destruct T; intuition. Qed.

(** Distributivity *)

Lemma next_or (φ ψ : LTL) : X (φ ∨ ψ) ≈ (X φ) ∨ (X ψ).
Proof. now ltl. Qed.

Lemma next_and (φ ψ : LTL) : X (φ ∧ ψ) ≈ (X φ) ∧ (X ψ).
Proof. now ltl. Qed.

Lemma next_until (φ ψ : LTL) : X (φ U ψ) ≈ (X φ) U (X ψ).
Proof. ltl; destruct T; intuition. Qed.

Lemma eventually_or (φ ψ : LTL) : ◇ (φ ∨ ψ) ≈ (◇ φ) ∨ (◇ ψ).
Proof. now ltl. Qed.

Lemma always_and (φ ψ : LTL) : □ (φ ∧ ψ) ≈ (□ φ) ∧ (□ ψ).
Proof. now ltl. Qed.

Lemma until_or (ρ φ ψ : LTL) : ρ U (φ ∨ ψ) ≈ (ρ U φ) ∨ (ρ U ψ).
Proof. now ltl. Qed.

Lemma and_until (ρ φ ψ : LTL) : (φ ∧ ψ) U ρ ≈ (φ U ρ) ∧ (ψ U ρ).
Proof. now ltl. Qed.

(** Negation propagation *)

Lemma not_not (φ : LTL) : ¬¬ φ ≈ φ.
Proof. now ltl. Qed.

Lemma not_and (φ ψ : LTL) : ¬ (φ ∧ ψ) ≈ ¬ φ ∨ ¬ ψ.
Proof.
  ltl.
  apply not_and_or.
  now intuition.
Qed.

Lemma not_or (φ ψ : LTL) : ¬ (φ ∨ ψ) ≈ ¬ φ ∧ ¬ ψ.
Proof. ltl. Qed.

Lemma not_next (φ : LTL) : ¬(X φ) ≈ X ¬φ.
Proof. ltl. Qed.

Lemma not_eventually (φ : LTL) : ¬(◇ φ) ≈ □ ¬φ.
Proof. ltl. Qed.

Lemma not_until_release (φ ψ : LTL) : ¬ (φ U ψ) ≈ ¬φ R ¬ψ.
Proof.
  ltl.
  apply imply_to_or; intros.
  intuition auto.
Qed.

Lemma not_always (φ : LTL) : ¬(□ φ) ≈ ◇ ¬φ.
Proof.
  ltl.
  apply imply_to_or; intros.
  intuition auto.
Qed.

Lemma not_release (φ ψ : LTL) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Proof.
  ltl.
  apply imply_to_or; intros.
  intuition auto.
Qed.

(** The equivalence of positive normal form holds under the strong
    assumption. *)
Lemma pnf_correct l : pnf l ≈ l.
Proof.
  symmetry.
  apply pnf_ind2'
    with (P:=fun x y => x ≈ y)
         (P0:=fun x y => ¬ x ≈ y);
  unfold ltl_equiv; simpl in *;
  intros; subst;
  try first [ reflexivity
            | assumption
            | now rewrite <- ?H, <- ?H0; ltl
            | now rewrite <- ?H; ltl
            | now rewrite ?H, ?H0; ltl
            | now rewrite ?H; ltl
            | now ltl ].
  - apply Accept_Proper.
    repeat intro; subst.
    unfold Basics.compose.
    split; intros.

  - now rewrite not_and, H, H0.
  - now rewrite not_and, H, H0.
  - now rewrite not_until_release, H, H0.
  - now rewrite not_release, H, H0.
  - now rewrite not_always, H.
Qed.

Lemma negate_correct l : negate l ≈ ¬ l.
Proof.
  symmetry.
  apply negate_ind2
    with (P:=fun x y => x ≈ y)
         (P0:=fun x y => ¬ x ≈ y);
  unfold ltl_equiv; simpl in *;
  intros; subst;
  try first [ reflexivity
            | assumption
            | now rewrite <- ?H, <- ?H0; ltl
            | now rewrite <- ?H; ltl
            | now rewrite ?H, ?H0; ltl
            | now rewrite ?H; ltl
            | now ltl ].
  - now rewrite not_and, H, H0.
  - now rewrite not_until_release, H, H0.
  - now rewrite not_release, H, H0.
  - now rewrite not_always, H.
Qed.

Ltac negated :=
  rewrite <- !negate_correct; simpl;
  rewrite !pnf_correct; simpl.

Lemma not_until_weak (φ ψ : LTL) : ¬ (φ U ψ) ≈ (φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ).
Proof.
  rewrite weakUntil_release.
  rewrite release_until.
  rewrite !not_and.
  rewrite !not_not.
  rewrite !not_or.
  rewrite !not_and.
  rewrite !not_not.
  now ltl.
Qed.

Lemma not_weakUntil (φ ψ : LTL) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Proof.
  unfold strongRelease.
  rewrite weakUntil_release.
  rewrite release_until.
  rewrite not_not.
  rewrite not_or.
  rewrite and_comm.
  reflexivity.
Qed.

Lemma not_strongRelease (φ ψ : LTL) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Proof.
  unfold strongRelease.
  rewrite weakUntil_release.
  rewrite release_until.
  rewrite not_not.
  rewrite not_or.
  rewrite !not_not.
  rewrite and_comm.
  reflexivity.
Qed.

(** Absorption laws *)

Lemma asborb_eventually (φ : LTL) : ◇ □ ◇ φ ≈ □ ◇ φ.
Proof. ltl; destruct T; intuition. Qed.

Lemma asborb_always (φ : LTL) : □ ◇ □ φ ≈ ◇ □ φ.
Proof. ltl; destruct T; intuition. Qed.

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

Lemma expand_until      (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ X(φ U ψ)).
Proof. now ltl. Qed.

Lemma expand_weakUntil  (φ ψ : LTL) : φ W ψ ≈ ψ ∨ (φ ∧ X(φ W ψ)).
Proof. now ltl. Qed.

Lemma expand_release    (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ X(φ R ψ)).
Proof. now ltl. Qed.

Lemma expand_always     (φ : LTL)   :   □ φ ≈ φ ∧ X(□ φ).
Proof. now ltl. Qed.

Lemma expand_eventually (φ : LTL)   :   ◇ φ ≈ φ ∨ X(◇ φ).
Proof. now ltl. Qed.

Lemma expand_correct l : expand l ≈ l.
Proof.
  induction l; simpl; intuition;
  rewrite ?IHl, ?IHl1, ?IHl2; try reflexivity.
  - symmetry; apply expand_until.
  - symmetry; apply expand_release.
  - symmetry; apply expand_eventually.
  - symmetry; apply expand_always.
Qed.

Lemma prune_correct l : prune l ≈ l.
Proof.
  apply prune_ind; simpl; intros; subst; intuition;
  try rewrite e0 in H;
  try rewrite e1 in H0.
  - rewrite <- H.
    now rewrite not_not.
  - now rewrite H.
  - rewrite <- H, H0.
    now ltl.
  - rewrite H, <- H0.
    now ltl.
  - now rewrite H, H0.
  - rewrite <- H, H0.
    now ltl.
  - rewrite H, <- H0.
    now ltl.
  - now rewrite H, H0.
  - now rewrite H.
  - now rewrite H, H0.
  - now rewrite H, H0.
  - now rewrite H.
  - now rewrite H.
Qed.

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

Fixpoint series {a} (l : list (LTL a)) : LTL a :=
  match l with
  | nil => ⊤
  | [x] => x
  | cons x xs => x ∧ Next (series xs)
  end.

Section Examples.

Variable s : Stream nat.

Open Scope ltl_scope.

Arguments Cons {_} _ _.

Definition num (n : nat) := Accept (fun x => if x =? n then ⊤ else ⊥).

Example ex_match_query  :
  matches nat (num 1 ∧ (X (num 2))) (Cons 1 (Cons 2 s)).
Proof. simpl; auto. Qed.

Example ex_match_series :
  matches nat (series [num 1; num 2]) (Cons 1 (Cons 2 s)).
Proof. simpl; auto. Qed.

Example ex_match_sample1 :
  matches nat (◇ (num 3 → ◇ (num 8)))
          (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 (Cons 6 (Cons 7 (Cons 8 (Cons 9 s))))))))).
Proof. simpl; intuition auto. Qed.

Example ex_match_sample2 :
  matches nat (◇ (ifThen (fun n => n =? 3) (fun n => ◇ (num (n + 5)))))
          (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 (Cons 6 (Cons 7 (Cons 8 (Cons 9 s))))))))).
Proof. simpl; intuition auto. Qed.

End Examples.
