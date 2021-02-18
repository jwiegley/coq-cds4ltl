Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.Lists.List
  Coq.Classes.Morphisms
  Coq.Logic.Classical
  FunInd
  Bool
  LTL.

Open Scope program_scope.
Open Scope list_scope.

Import ListNotations.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Module Type StreamType.

Parameter a : Type.              (* The type of entries in the trace *)

End StreamType.

Module LTL (S : StreamType) <: LinearTemporalLogicW <: LinearTemporalLogic.

(** This data type encodes the syntax of LTL in Positive Normal Form (PNF). *)
Inductive Formula : Type :=
  (* Boolean layer *)
  | Top
  | Bottom

  | Examine (v : S.a -> Formula)

  | And   (p q : Formula)
  | Or    (p q : Formula)

  (* Temporal layer *)
  | Next       (p : Formula)

  | Until      (p q : Formula)
  | Release    (p q : Formula)

  | Always     (p : Formula)
  | Eventually (p : Formula)

  | Wait          (p q : Formula)
  | StrongRelease (p q : Formula).

Definition t := Formula.

Fixpoint size (p : t) : nat :=
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

Function negate (l : t) : t :=
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

Fixpoint expand (l : t) : t :=
  match l with
  | Top               => l
  | Bottom            => l

  | Examine v         => Examine (expand ∘ v)

  | And p q           => And (expand p) (expand q)
  | Or p q            => Or (expand p) (expand q)

  | Next p            => Next (expand p)

  | Until p q         => Or (expand q) (And (expand p) (Next (Until p q)))
  | Release p q       => And (expand q) (Or (expand p) (Next (Release p q)))

  (* jww (2021-02-18): NYI *)
  | Always p          => And (expand p) (Next (Always p))
  | Eventually p      => Or (expand p) (Next (Eventually p))

  | Wait p q          => Or (expand q) (And (expand p) (Next (Until p q)))
  | StrongRelease p q => And (expand q) (Or (expand p) (Next (Release p q)))
  end.

Definition basic (l : t) : Prop :=
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

Fixpoint shallow (l : t) : Prop :=
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

Lemma expand_complete (l : t) : shallow (expand l).
Proof. induction l; simpl in *; intuition auto. Qed.

(** Prune out any instances of Top or Bottom *)
Function prune (l : t) : t :=
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

Fixpoint matches (n : Prop) (l : t) (s : list S.a) {struct l} : Prop :=
  match l with
  | Top    => True
  | Bottom => False

  | Examine v =>
    match s with
    | []     => n
    | x :: _ => matches n (v x) s
    end

  | And p q => matches n p s /\ matches n q s
  | Or p q  => matches n p s \/ matches n q s

  | Next p =>
    match s with
    | []      => matches n p []
    | x :: xs => matches n p xs
    end

  | Until p q =>
    let fix go s :=
        match s with
        | [] => matches n q s
        | _ :: xs => matches n q s \/ (matches n p s /\ go xs)
        end in go s

  | Release p q =>
    let fix go s :=
        match s with
        | [] => matches n q s
        | _ :: xs => matches n q s /\ (matches n p s \/ go xs)
        end in go s

  | Always p =>
    let fix go s :=
        match s with
        | [] => True
        | _ :: xs => matches n p s /\ go xs
        end in go s

  | Eventually p =>
    let fix go s :=
        match s with
        | [] => False
        | _ :: xs => matches n p s \/ go xs
        end in go s

  | Wait p q =>
    let fix go s :=
        match s with
        | [] => True
        | _ :: xs => matches n q s \/ (matches n p s /\ go xs)
        end in go s

  | StrongRelease p q =>
    let fix go s :=
        match s with
        | [] => False
        | _ :: xs => matches n q s /\ (matches n p s \/ go xs)
        end in go s
  end.

Definition true           := Top.
Definition false          := Bottom.
Definition and            := And.
Definition or             := Or.
Definition not            := negate.
Definition implies        := fun p q => forall n s, matches n p s -> matches n q s.
Definition equivalent     := fun p q => implies p q /\ implies q p.
Definition next           := Next.
Definition until          := Until.
Definition release        := Release.
Definition always         := Always.
Definition eventually     := Eventually.
Definition wait           := Wait.
Definition strong_release := StrongRelease.
Definition examine        := Examine.

Declare Scope boolean_scope.
Bind Scope boolean_scope with t.
Delimit Scope boolean_scope with boolean.
Open Scope boolean_scope.

Notation "¬ p"    := (not p)         (at level 75, right associativity) : boolean_scope.
Infix    "∨"      := or              (at level 85, right associativity) : boolean_scope.
Notation "p ⇒ q"  := (¬ p ∨ q)       (at level 86, right associativity) : boolean_scope.
Notation "⊤"      := true            (at level 0, no associativity) : boolean_scope.
Notation "⊥"      := false           (at level 0, no associativity) : boolean_scope.
Infix    "∧"      := and             (at level 80, right associativity) : boolean_scope.
Infix    "⟹"     := implies         (at level 99, right associativity) : boolean_scope.
Infix    "≈"      := equivalent      (at level 90, no associativity) : boolean_scope.

Declare Scope ltl_scope.
Bind Scope ltl_scope with t.
Delimit Scope ltl_scope with ltl.
Open Scope boolean_scope.
Open Scope ltl_scope.

Notation "◯ p"       := (next p)             (at level 75, right associativity) : ltl_scope.
Notation "◇ p"       := (eventually p)       (at level 75, right associativity) : ltl_scope.
Notation "□ p"       := (always p)           (at level 75, right associativity) : ltl_scope.
Notation "p 'U' q"   := (until p q)          (at level 79, right associativity) : ltl_scope.
Notation "p 'W' q"   := (wait p q)           (at level 79, right associativity) : ltl_scope.
Notation "p 'R' q"   := (release p q)        (at level 79, right associativity) : ltl_scope.
Notation "p 'M' q"   := (strong_release p q) (at level 79, right associativity) : ltl_scope.
Notation "'Λ' f , g" := (examine (λ f , g))  (at level 97, no associativity) : ltl_scope.

Program Instance implies_reflexive : Reflexive implies.
Next Obligation. now repeat intro. Qed.

Program Instance implies_transitive : Transitive implies.
Next Obligation.
  repeat intro.
  now apply H0, H.
Qed.

Program Instance Equivalence_equivalent : Equivalence equivalent.
Next Obligation. split; repeat intro; auto. Qed.
Next Obligation. split; repeat intro; firstorder. Qed.
Next Obligation. split; repeat intro; firstorder. Qed.

Program Instance equivalent_respects_equivalent :
  Proper (equivalent ==> equivalent ==> iff) equivalent.
Next Obligation.
  split; repeat intro.
  - now rewrite <- H0, <- H1, <- H.
  - now rewrite H0, <- H1.
Qed.

Program Instance Examine_respects_implies :
  Proper ((eq ==> implies) ==> implies) Examine.
Next Obligation.
  repeat intro; simpl in *.
  destruct s; intuition.
  now apply (H a a (reflexivity _)).
Qed.

Program Instance Examine_respects_equivalent :
  Proper ((eq ==> equivalent) ==> equivalent) Examine.
Next Obligation.
  split; repeat intro.
  - destruct s; intuition.
    now apply (H a a (reflexivity _)).
  - destruct s; intuition.
    now apply (H a a (reflexivity _)).
Qed.

Program Instance matches_respects_implies (n : Prop) :
  Proper (implies ==> eq ==> Basics.impl) (matches n).
Next Obligation.
  repeat intro.
  subst.
  now apply H.
Qed.

Program Instance matches_respects_equivalent (n : Prop) :
  Proper (equivalent ==> eq ==> iff) (matches n).
Next Obligation.
  split; repeat intro.
  - subst.
    now apply H.
  - subst.
    now apply H.
Qed.

Program Instance And_respects_implies : Proper (implies ==> implies ==> implies) And.
Next Obligation.
  repeat intro.
  simpl.
  now rewrite <- H, <- H0.
Qed.

Program Instance And_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) And.
Next Obligation.
  split; repeat intro.
  - destruct H, H0.
    now rewrite <- H, <- H0.
  - destruct H, H0.
    now rewrite <- H2, <- H3.
Qed.

Program Instance Or_respects_implies : Proper (implies ==> implies ==> implies) Or.
Next Obligation.
  repeat intro.
  simpl.
  now rewrite <- H, <- H0.
Qed.

Program Instance Or_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) Or.
Next Obligation.
  split; repeat intro.
  - destruct H, H0.
    now rewrite <- H, <- H0.
  - destruct H, H0.
    now rewrite <- H2, <- H3.
Qed.

Program Instance Next_respects_implies : Proper (implies ==> implies) Next.
Next Obligation.
  repeat intro.
  simpl.
  destruct s;
  now rewrite <- H.
Qed.

Program Instance Next_respects_equivalent : Proper (equivalent ==> equivalent) Next.
Next Obligation.
  split; repeat intro.
  - simpl.
    destruct s;
    now rewrite <- H.
  - simpl.
    destruct s;
    now rewrite H.
Qed.

Program Instance Until_respects_implies : Proper (implies ==> implies ==> implies) Until.
Next Obligation.
Admitted.

Program Instance Until_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) Until.
Next Obligation.
Admitted.

Program Instance Release_respects_implies : Proper (implies ==> implies ==> implies) Release.
Next Obligation.
Admitted.

Program Instance Release_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) Release.
Next Obligation.
Admitted.

Program Instance Always_respects_implies : Proper (implies ==> implies) Always.
Next Obligation.
Admitted.

Program Instance Always_respects_equivalent : Proper (equivalent ==> equivalent) Always.
Next Obligation.
Admitted.

Program Instance Eventually_respects_implies : Proper (implies ==> implies) Eventually.
Next Obligation.
Admitted.

Program Instance Eventually_respects_equivalent : Proper (equivalent ==> equivalent) Eventually.
Next Obligation.
Admitted.

Program Instance Wait_respects_implies : Proper (implies ==> implies ==> implies) Wait.
Next Obligation.
Admitted.

Program Instance Wait_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) Wait.
Next Obligation.
Admitted.

Program Instance StrongRelease_respects_implies : Proper (implies ==> implies ==> implies) StrongRelease.
Next Obligation.
Admitted.

Program Instance StrongRelease_respects_equivalent : Proper (equivalent ==> equivalent ==> equivalent) StrongRelease.
Next Obligation.
Admitted.

Lemma expand_until (φ ψ : Formula) : φ U ψ ≈ ψ ∨ (φ ∧ ◯ (φ U ψ)).
Proof.
Admitted.

Lemma expand_release (φ ψ : Formula) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).
Proof.
Admitted.

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
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma prune_correct l : prune l ≈ l.
Proof.
  apply prune_ind; simpl; intros; subst; intuition;
  try rewrite e0 in H;
  try rewrite e1 in H0.
Admitted.

Lemma matches_negate n x s : matches n (negate x) s <-> ~ matches (~ n) x s.
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
      induction s.
        simpl in *; firstorder.
        now apply NNPP.
      simpl matches in H0.
      now simpl in *; firstorder.
    + simpl in *.
      apply not_and_or in H.
      now intuition.
    + simpl in *.
      now destruct s; intuition.
    + simpl negate.
      induction s.
        simpl in *; intuition.
      simpl matches in H.
      apply not_or_and in H.
      destruct H.
      apply not_and_or in H0.
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        simpl in *; intuition.
      simpl matches in H.
      apply not_and_or in H.
      destruct H;
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        simpl in *; intuition.
      simpl matches in H.
      apply not_and_or in H.
      destruct H;
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        simpl in *; intuition.
      simpl matches in H.
      apply not_or_and in H.
      destruct H;
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        simpl in *; intuition.
      simpl matches in H.
      apply not_or_and in H.
      destruct H.
      apply not_and_or in H0.
      now simpl in *; intuition.
    + simpl negate.
      induction s.
        simpl in *; intuition.
      simpl matches in H.
      apply not_and_or in H.
      destruct H;
      now simpl in *; intuition.
Qed.

Program Instance negate_respects_implies : Proper (implies --> implies) negate | 1.
Next Obligation.
  repeat intro.
  unfold flip in H.
  apply matches_negate.
  apply matches_negate in H0.
  intro.
  apply H in H1.
  contradiction.
Qed.

Program Instance not_respects_implies : Proper (implies --> implies) not | 1.
Next Obligation.
  unfold not.
  repeat intro.
  now rewrite <- H.
Qed.

(** These instances allow us to rewrite without unfolding. *)
Instance and_respects_implies :
  Proper (implies ==> implies ==> implies) and := And_respects_implies.
Instance and_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) and := And_respects_equivalent.
Instance or_respects_implies :
  Proper (implies ==> implies ==> implies) or := Or_respects_implies.
Instance or_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) or := Or_respects_equivalent.
Instance next_respects_implies :
  Proper (implies ==> implies) next := Next_respects_implies.
Instance next_respects_equivalent :
  Proper (equivalent ==> equivalent) next := Next_respects_equivalent.
Instance until_respects_implies :
  Proper (implies ==> implies ==> implies) until := Until_respects_implies.
Instance until_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) until := Until_respects_equivalent.
Instance eventually_respects_implies :
  Proper (implies ==> implies) eventually := Eventually_respects_implies.
Instance eventually_respects_equivalent :
  Proper (equivalent ==> equivalent) eventually := Eventually_respects_equivalent.
Instance always_respects_implies :
  Proper (implies ==> implies) always := Always_respects_implies.
Instance always_respects_equivalent :
  Proper (equivalent ==> equivalent) always := Always_respects_equivalent.
Instance wait_respects_implies :
  Proper (implies ==> implies ==> implies) wait := Wait_respects_implies.
Instance wait_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) wait := Wait_respects_equivalent.
Instance release_respects_implies :
  Proper (implies ==> implies ==> implies) release := Release_respects_implies.
Instance release_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) release := Release_respects_equivalent.
Instance strong_release_respects_implies :
  Proper (implies ==> implies ==> implies) strong_release := StrongRelease_respects_implies.
Instance strong_release_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) strong_release := StrongRelease_respects_equivalent.

Theorem or_inj (p q : t) : p ⟹ p ∨ q.
Proof.
Admitted.

Theorem true_def (p : t) : p ∨ ¬p ≈ ⊤.
Proof.
Admitted.

Theorem false_def (p : t) : ¬(p ∨ ¬p) ≈ ⊥.
Proof.
Admitted.

Theorem or_comm (p q : t) : p ∨ q ≈ q ∨ p.
Proof.
Admitted.

Theorem or_assoc (p q r : t) : (p ∨ q) ∨ r ≈ p ∨ (q ∨ r).
Proof.
Admitted.

Theorem and_def (p q : t) : p ∧ q ≈ ¬(¬p ∨ ¬q).
Proof.
Admitted.

Theorem huntington (p q : t) : ¬(¬p ∨ ¬q) ∨ ¬(¬p ∨ q) ≈ p.
Proof.
Admitted.

Theorem next_not (p : t) : ◯ ¬p ≈ ¬◯ p.
Proof.
Admitted.

Theorem next_impl (p q : t) : ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Proof.
Admitted.

Theorem next_until (p q : t) : ◯ (p U q) ≈ (◯ p) U (◯ q).
Proof.
Admitted.

Theorem until_expansion (p q : t) : p U q ≈ q ∨ (p ∧ ◯ (p U q)).
Proof.
Admitted.

Theorem until_right_bottom (p : t) : p U ⊥ ≈ ⊥.
Proof.
Admitted.

Theorem until_left_or (p q r : t) : p U (q ∨ r) ≈ (p U q) ∨ (p U r).
Proof.
Admitted.

Theorem until_right_or (p q r : t) : (p U r) ∨ (q U r) ⟹ (p ∨ q) U r.
Proof.
Admitted.

Theorem until_left_and (p q r : t) : p U (q ∧ r) ⟹ (p U q) ∧ (p U r).
Proof.
Admitted.

Theorem until_right_and (p q r : t) : (p ∧ q) U r ≈ (p U r) ∧ (q U r).
Proof.
Admitted.

Theorem until_impl_order (p q r : t) : (p U q) ∧ (¬q U r) ⟹ p U r.
Proof.
Admitted.

Theorem until_right_or_order (p q r : t) : p U (q U r) ⟹ (p ∨ q) U r.
Proof.
Admitted.

Theorem until_right_and_order (p q r : t) : p U (q ∧ r) ⟹ (p U q) U r.
Proof.
Admitted.

Theorem not_until (p q : t) : ⊤ U ¬p ∧ ¬(p U q) ≈ ¬q U (¬p ∧ ¬q).
Proof.
Admitted.

Theorem evn_def (p : t) : ◇ p ≈ ⊤ U p.
Proof.
Admitted.

Theorem always_def (p : t) : □ p ≈ ¬◇ ¬p.
Proof.
Admitted.

Theorem always_induction_ (p : t) : □ (p ⇒ ◯ p) ⟹ p ⇒ □ p.
Proof.
Admitted.

Theorem always_until_and_ind (p q r : t) :
  □ (p ⇒ (◯ p ∧ q) ∨ r) ⟹ p ⇒ □ q ∨ q U r.
Proof.
Admitted.

Theorem always_and_until (p q r : t) : □ p ∧ q U r ⟹ (p ∧ q) U (p ∧ r).
Proof.
Admitted.

Theorem wait_def (p q : t) : p W q ≈ □ p ∨ p U q.
Proof.
Admitted.

Theorem release_def (p q : t) : p R q ≈ ¬(¬p U ¬q).
Proof.
Admitted.

Theorem strong_release_def (p q : t) : p M q ≈ p U (q ∧ p).
Proof.
Admitted.

End LTL.

Module LTLCombinators (S : StreamType).

Module Import L := LTL S.
Include L.

Definition if_then (p : S.a -> bool) (f : S.a -> t) :=
  Examine (fun x => if p x then f x else ⊤).

Fixpoint series (l : list t) : t :=
  match l with
  | nil => ⊤
  | [x] => x
  | x :: xs => x ∧ Next (series xs)
  end.

End LTLCombinators.

Require Import Coq.Arith.PeanoNat.

Module NatStream <: StreamType.

Definition a := nat.

End NatStream.

Module LTLExamples.

Module Import L := LTL NatStream.
Module Import C := LTLCombinators NatStream.
Include L.

Definition num (n : nat) := Examine (λ x, if x =? n then ⊤ else ⊥).

Example ex_match_query  :
  matches (num 1 ∧ (◯ (num 2))) [1; 2].
Proof. simpl; auto. Qed.

Example ex_match_series :
  matches (series [num 1; num 2]) [1; 2].
Proof. simpl; auto. Qed.

Example ex_match_sample1 :
  matches (◇ (num 3 ⇒ ◇ (num 8))) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. simpl; intuition auto. Qed.

Example ex_match_sample2 :
  matches (◇ (if_then (fun n => n =? 3) (fun n => ◇ (num (n + 5)))))
          [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. simpl; intuition auto. Qed.

End LTLExamples.
