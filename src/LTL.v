Require Import
  Coq.Classes.Morphisms
  MinLTL.

Module Type LinearTemporalLogic.

Declare Module MinLTL : MinimalLinearTemporalLogic.
Include MinLTL.

Parameter eventually : t -> t.
Parameter always : t -> t.
Parameter wait : t -> t -> t.
Parameter release : t -> t -> t.

Declare Instance eventually_equiv : Proper (equiv ==> equiv) eventually.
Declare Instance always_equiv : Proper (equiv ==> equiv) always.
Declare Instance wait_equiv : Proper (equiv ==> equiv ==> equiv) wait.
Declare Instance release_equiv : Proper (equiv ==> equiv ==> equiv) release.

Global Notation "◇ p"     := (eventually p)  (at level 0).
Global Notation "□ p"     := (always p)      (at level 0).
Global Notation "p 'W' q" := (wait p q)      (at level 45).
Global Notation "p 'R' q" := (release p q)   (at level 45).

(*** 3.3 Eventually *)

Hypothesis (* 38 *) eventually_def : forall (φ : t), ◇ φ ≈ ⊤ U φ.

(* Lemmas 39-53 *)

(*** 3.4 Always *)

Hypothesis (* 54 *) always_def : forall (φ : t), □ φ ≈ ¬◇¬ φ.
Hypothesis (* 55 *) always_until_ind : forall (φ ψ χ : t), □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ φ → □ ψ ∨ (ψ U χ).
Hypothesis (* 56 *) always_until_ind2 : forall (φ ψ : t), □ (φ → ◯ (φ ∨ ψ)) ⟹ φ → □ φ ∨ (φ U ψ).

(* Lemmas 57-81 *)

(*** 3.5 Temporal Deduction *)

(* Lemma 82 *)

(*** 3.6 Always, Continued *)

(* Lemmas 83-135 *)

(*** 3.7 Proof Metatheorems *)

(* Lemmas 136-139 *)

(*** 3.8 Always, Continued *)

(* Lemmas 140-168 *)

(*** 3.9 Wait *)

Hypothesis (* 169 *) wait_def : forall (φ ψ : t), φ W ψ ≈ □ φ ∨ (φ U ψ).
Hypothesis (* 170 *) wait_distr_not : forall (φ ψ : t), ¬(φ W ψ) ≈ ¬ ψ U (¬ φ ∧ ¬ ψ).

(* Lemmas 171-254 *)

End LinearTemporalLogic.
