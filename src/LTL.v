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
Parameter strong_release : t -> t -> t.

Declare Instance eventually_respects_impl :
  Proper (impl ==> impl) eventually.
Declare Instance always_respects_impl :
  Proper (impl ==> impl) always.
Declare Instance wait_respects_impl :
  Proper (impl ==> impl ==> impl) wait.
Declare Instance release_respects_impl :
  Proper (impl ==> impl ==> impl) release.

Notation "◇ p"     := (eventually p)       (at level 0, right associativity).
Notation "□ p"     := (always p)           (at level 0, right associativity).
Notation "p 'W' q" := (wait p q)           (at level 44, right associativity).
Notation "p 'R' q" := (release p q)        (at level 44, right associativity).
Notation "p 'M' q" := (strong_release p q) (at level 44, right associativity).

(*** 3.3 Eventually *)

Hypothesis (* 38 *) eventually_def : forall (φ : t), ◇ φ ≈ ⊤ U φ.

Set Nested Proofs Allowed.

Lemma (* 39 *) law (φ ψ : t) : (φ U ψ) ∧ ◇ ψ ≈ φ U ψ.
Lemma (* 40 *) law (φ ψ : t) : (φ U ψ) ∨ ◇ ψ ≈ ◇ ψ.
Lemma (* 41 *) law (φ ψ : t) : φ U ◇ ψ ≈ ◇ ψ.
Lemma (* 42 *) law (φ ψ : t) : φ U ψ ⟹ ◇ ψ.
Lemma (* 43 *) law : ◇ ⊤ ≈ ⊤.
Lemma (* 44 *) law : ◇ ⊥ ≈ ⊥.
Lemma (* 45 *) law (φ : t) : ◇ φ ≈ φ ∨ ◯◇ φ.
Lemma (* 46 *) law (φ : t) : φ ⟹ ◇ φ.
Lemma (* 47 *) law (φ : t) : ◯ φ ⟹ ◇ φ.
Lemma (* 48 *) law (φ : t) : φ ∨ ◇ φ ≈ ◇ φ.
Lemma (* 49 *) law (φ : t) : ◇ φ ∧ φ ≈ φ.
Lemma (* 50 *) law (φ : t) : ◇◇ φ ≈ ◇ φ.
Lemma (* 51 *) law (φ : t) : ◯◇ φ ≈ ◇◯ φ.
Lemma (* 52 *) law (φ ψ : t) : ◇ (φ ∨ ψ) ⟹ ◇ φ ∨ ◇ ψ.
Lemma (* 53 *) law (φ ψ : t) : ◇ (φ ∧ ψ) ⟹ ◇ φ ∧ ◇ ψ.

(*** 3.4 Always *)

Hypothesis (* 54 *) always_def : forall (φ : t), □ φ ≈ ¬◇¬ φ.
Hypothesis (* 55 *) always_until_and_ind : forall (φ ψ χ : t),
  □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ φ → □ ψ ∨ (ψ U χ).
Hypothesis (* 56 *) always_until_or_ind : forall (φ ψ : t),
  □ (φ → ◯ (φ ∨ ψ)) ⟹ φ → □ φ ∨ (φ U ψ).

Lemma (* 57 *) law (φ : t) : □ (φ → ◯ φ) ⟹ φ → □ φ.
Lemma (* 58 *) law (φ : t) : □ (◯ φ → φ) ⟹ ◇ φ → φ.
Lemma (* 59 *) law (φ : t) : ◇ φ ≈ ¬□¬ φ.
Lemma (* 60 *) law (φ : t) : ¬□ φ ≈ ◇¬ φ.
Lemma (* 61 *) law (φ : t) : ¬◇ φ ≈ □¬ φ.
Lemma (* 62 *) law (φ : t) : ¬◇□ φ ≈ □◇¬ φ.
Lemma (* 63 *) law (φ : t) : ¬□◇ φ ≈ ◇□¬ φ.
Lemma (* 64 *) law : □ ⊤ ≈ ⊤.
Lemma (* 65 *) law : □ ⊥ ≈ ⊥.
Lemma (* 66 *) law (φ : t) : □ φ ≈ φ ∧ ◯□ φ.
Lemma (* 67 *) law (φ : t) : □ φ ≈ φ ∧ ◯ φ ∧ ◯□ φ.
Lemma (* 68 *) law (φ : t) : φ ∧ □ φ ≈ □ φ.
Lemma (* 69 *) law (φ : t) : □ φ ∨ φ ≈ φ.
Lemma (* 70 *) law (φ : t) : ◇ φ ∧ □ φ ≈ □ φ.
Lemma (* 71 *) law (φ : t) : □ φ ∨ ◇ φ ≈ ◇ φ.
Lemma (* 72 *) law (φ : t) : □□ φ ≈ □ φ.
Lemma (* 73 *) law (φ : t) : ◯□ φ ≈ □◯ φ.
Lemma (* 74 *) law (φ : t) : φ → □ φ ⟹ φ → ◯□ φ.
Lemma (* 75 *) law (φ : t) : φ ∧ ◇¬ φ ⟹ ◇ (φ ∧ ◯¬ φ).
Lemma (* 76 *) law (φ : t) : □ φ ⟹ φ.
Lemma (* 77 *) law (φ : t) : □ φ ⟹ ◇ φ.
Lemma (* 78 *) law (φ : t) : □ φ ⟹ ◯ φ.
Lemma (* 79 *) law (φ : t) : □ φ ⟹ ◯□ φ.
Lemma (* 80 *) law (φ : t) : □ φ ⟹ □◯ φ.
Lemma (* 81 *) law (φ ψ : t) : □ φ ⟹ ¬ (ψ U ¬ φ).

(*** 3.5 Temporal Deduction *)

Lemma (* 82 *) temporal_deduction (φ ψ : t) : (φ ≈ ⊤ -> ψ ≈ ⊤) -> □ φ ⟹ ψ.
Proof.
Admitted.

(*** 3.6 Always, Continued *)

Lemma (* 83 *) law (φ ψ χ : t) : □ φ ∧ (ψ U χ) ⟹ (φ ∧ ψ) U (φ ∧ χ).
Proof.
  apply and_impl_iff.
  apply temporal_deduction; intros.
  rewrite H.
  rewrite !true_and.
  rewrite or_comm.
  now apply true_def.
Qed.

(* Lemmas 84-135 (52) *)

(*** 3.7 Proof Metatheorems *)

(*
Lemma (* 136 *) metatheorem (ϕ : t) : ϕ is a theorem <-> □ ϕ is a theorem.
*)

Lemma (* 137 *) next_metatheorem (φ ψ : t) : φ ⟹ ψ -> ◯ φ ⟹ ◯ ψ.
Proof. now apply next_respects_impl. Qed.

Lemma (* 138 *) eventually_metatheorem (φ ψ : t) : φ ⟹ ψ -> ◇ φ ⟹ ◇ ψ.
Proof. now apply eventually_respects_impl. Qed.

Lemma (* 139 *) always_metatheorem (φ ψ : t) : φ ⟹ ψ -> □ φ ⟹ □ ψ.
Proof. now apply always_respects_impl. Qed.

(*** 3.8 Always, Continued *)

(* Lemmas 140-168 (28) *)

(*** 3.9 Wait *)

Hypothesis (* 169 *) wait_def : forall (φ ψ : t), φ W ψ ≈ □ φ ∨ (φ U ψ).
Hypothesis (* 170 *) wait_distr_not : forall (φ ψ : t), ¬(φ W ψ) ≈ ¬ ψ U (¬ φ ∧ ¬ ψ).

(* Lemmas 171-254 (84) *)

End LinearTemporalLogic.
