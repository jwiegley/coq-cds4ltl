Require Import
  Coq.Classes.Morphisms
  Bool.

(***********************************************************************
 *
 * This Linear Temporal Logic follows directly from the paper:
 *
 * "A Calculational Deductive System for Linear Temporal Logic"
 * https://dl.acm.org/doi/10.1145/3387109
 *
 * by Warford, Vega and Staley
 *)

Module Type MinimalLinearTemporalLogic.

Declare Module Bool : BooleanLogic.
Include Bool.

Parameter next : t -> t.
Parameter until : t -> t -> t.

Declare Instance next_equiv : Proper (equiv ==> equiv) next.
Declare Instance until_equiv : Proper (equiv ==> equiv ==> equiv) until.

Notation "◯ p"     := (next p)    (at level 0).
Notation "p 'U' q" := (until p q) (at level 45).

(*** 3.1 Next *)

Hypothesis (* 1 *) next_self_dual : forall (φ : t), ◯¬ φ ≈ ¬◯ φ.
Hypothesis (* 2 *) next_distr_impl : forall (φ ψ : t), ◯ (φ → ψ) ≈ ◯ φ → ◯ ψ.

Lemma (* 3 *) next_linearity (φ : t) : ◯ φ ≈ ¬◯¬ φ.
Proof.
  rewrite next_self_dual.
  now apply not_swap.
Qed.

Lemma (* 4 *) next_distr_or (φ ψ : t) : ◯ (φ ∨ ψ) ≈ ◯ φ ∨ ◯ ψ.
Proof.
  pose proof (next_distr_impl (¬ φ) ψ) as H; rewrite not_not in H.
  rewrite H.
  now rewrite <- next_linearity.
Qed.

Lemma (* 5 *) next_distr_and (φ ψ : t) : ◯ (φ ∧ ψ) ≈ ◯ φ ∧ ◯ ψ.
Proof.
  rewrite <- (not_not φ) at 1.
  rewrite <- (not_not ψ) at 1.
  rewrite <- not_or.
  rewrite next_self_dual.
  rewrite next_distr_or.
  rewrite not_or.
  now rewrite <- !next_linearity.
Qed.

Lemma (* 6 *) next_distr_next_eq (φ ψ : t) : ◯ (φ ≡ ψ) ≈ ◯ φ ≡ ◯ ψ.
Proof.
  rewrite next_distr_or.
  rewrite not_or.
  rewrite next_distr_and.
  rewrite next_self_dual.
  rewrite next_self_dual.
  rewrite not_and.
  rewrite next_distr_or.
  rewrite next_self_dual.
  rewrite <- not_and.
  now rewrite <- not_or.
Qed.

Lemma (* 7 *) next_top : ◯ (⊤) ≈ ⊤.
Proof.
  rewrite (true_def ⊤) at 1.
  rewrite next_distr_or.
  rewrite next_self_dual.
  now rewrite <- true_def.
Qed.

Lemma (* 8 *) next_bottom : ◯ (⊥) ≈ ⊥.
Proof.
  rewrite (false_def ⊥) at 1.
  rewrite next_self_dual.
  rewrite next_distr_or.
  rewrite next_self_dual.
  now rewrite <- false_def.
Qed.

(*** 3.2 Until *)

Hypothesis (* 9 *) next_distr_until : forall (φ ψ : t), ◯ (φ U ψ) ≈ (◯ φ) U (◯ ψ).
Hypothesis (* 10 *) until_expansion : forall (φ ψ : t), φ U ψ ≈ ψ ∨ (φ ∧ ◯ (φ U ψ)).
Hypothesis (* 11 *) until_right_bottom : forall (φ : t), φ U ⊥ ≈ ⊥.
Hypothesis (* 12 *) until_left_distr_or : forall (φ ψ χ : t), φ U (ψ ∨ χ) ≈ (φ U ψ) ∨ (φ U χ).
Hypothesis (* 13 *) until_right_distr_or : forall (φ ψ χ : t), (φ U χ) ∨ (ψ U χ) ⟹ (φ ∨ ψ) U χ.
Hypothesis (* 14 *) until_left_distr_and : forall (φ ψ χ : t), φ U (ψ ∧ χ) ⟹ (φ U ψ) ∧ (φ U χ).
Hypothesis (* 15 *) until_right_distr_and : forall (φ ψ χ : t), (φ ∧ ψ) U χ ≈ (φ U χ) ∧ (ψ U χ).
Hypothesis (* 16 *) until_impl_order : forall (φ ψ χ : t), (φ U ψ) ∧ (¬ ψ U χ) ⟹ φ U χ.
Hypothesis (* 17 *) until_right_or_order : forall (φ ψ χ : t), φ U (ψ U χ) ⟹ (φ ∨ ψ) U χ.
Hypothesis (* 18 *) until_right_and_order : forall (φ ψ χ : t), φ U (ψ ∧ χ) ⟹ φ U (ψ U χ).

(* Lemmas 19-37 *)

Lemma (* 19 *) until_right_distr_impl (φ ψ χ : t) : (φ → ψ) U χ ⟹ (φ U χ) → (ψ U χ).
Proof.
Admitted.

Lemma (* 20 *) until_right_top (φ : t) : φ U ⊤ ≈ ⊤.
Proof.
  rewrite until_expansion.
  rewrite or_comm.
  now rewrite or_true.
Qed.

Lemma (* 21 *) until_left_bottom (φ : t) : ⊥ U φ ≈ φ.
Proof.
  rewrite until_expansion.
  rewrite and_comm.
  rewrite and_false.
  now rewrite or_false.
Qed.

Lemma (* 22 *) until_idem (φ : t) : φ U φ ≈ φ.
Proof.
  rewrite until_expansion.
  now rewrite or_absorb.
Qed.

Lemma (* 23 *) until_excl_middle (φ ψ : t) : (φ U ψ) ∨ (φ U ¬ ψ) ≈ ⊤.
Proof.
  rewrite <- until_left_distr_or.
  rewrite <- true_def.
  now apply until_right_top.
Qed.

Lemma (* 24 *) until_24 (φ ψ χ : t) : (¬ φ U (ψ U χ)) ∧ (φ U χ) ⟹ ψ U χ.
Proof.
  rewrite until_right_or_order.
  rewrite until_right_distr_impl.
  rewrite and_comm.
  rewrite distr_or_and.
  rewrite absurdity.
  rewrite or_comm.
  rewrite or_false.
  rewrite and_comm.
  now rewrite and_proj.
Qed.

Lemma (* 25 *) until_25 (φ ψ χ : t) : (φ U (¬ ψ U χ)) ∧ (ψ U χ) ⟹ φ U χ.
Admitted.

Lemma (* 26 *) until_26 (φ ψ : t) : (φ U ψ) ∧ (¬ ψ U φ) ⟹ φ.
Admitted.

Lemma (* 27 *) until_27 (φ ψ : t) : φ ∧ (¬ φ U ψ) ⟹ ψ.
Proof.
  rewrite <- (until_idem φ) at 1.
  rewrite until_impl_order.
Admitted.

Lemma (* 28 *) until_28 (φ ψ : t) : φ U ψ ⟹ φ ∨ ψ.
Proof.
  rewrite until_expansion.
  rewrite distr_and_or.
  rewrite and_proj.
  rewrite or_comm.
  reflexivity.
Qed.

Lemma (* 29 *) until_insertion (φ ψ : t) : ψ ⟹ φ U ψ.
Proof.
  rewrite until_expansion.
  now apply or_inj.
Qed.

Lemma (* 30 *) until_30 (φ ψ : t) : φ ∧ ψ ⟹ φ U ψ.
Proof.
  rewrite until_expansion.
  rewrite <- or_inj.
  rewrite and_comm.
  now apply and_proj.
Qed.

Lemma (* 31 *) until_absorb_or_u (φ ψ : t) : φ ∨ (φ U ψ) ≈ φ ∨ ψ.
Proof.
  apply equiv_def; split.
  - rewrite (until_28 φ ψ) at 1.
    rewrite <- or_assoc.
    now rewrite or_idem.
  - now rewrite <- until_insertion.
Qed.

Lemma (* 32 *) until_absorb_u_or (φ ψ : t) : (φ U ψ) ∨ ψ ≈ φ U ψ.
Proof.
  rewrite until_expansion.
  rewrite or_comm at 1.
  rewrite <- or_assoc.
  now rewrite or_idem.
Qed.

Lemma (* 33 *) until_absorb_u_and (φ ψ : t) : (φ U ψ) ∧ ψ ≈ ψ.
Proof.
  apply equiv_def; split.
  - rewrite and_comm.
    now apply and_proj.
  - rewrite <- and_idem at 1.
    now rewrite (until_insertion φ ψ) at 1.
Qed.

Lemma (* 34 *) until_absorb_u_or_and (φ ψ : t) : (φ U ψ) ∨ (φ ∧ ψ) ≈ φ U ψ.
Proof.
  apply equiv_def; split.
  - rewrite until_30.
    now rewrite or_idem.
  - now rewrite <- or_inj.
Qed.

Lemma (* 35 *) until_absorb_u_and_or (φ ψ : t) : (φ U ψ) ∧ (φ ∨ ψ) ≈ φ U ψ.
Proof.
  apply equiv_def; split.
  - now apply and_proj.
  - rewrite <- until_28.
    now rewrite and_idem.
Qed.

Lemma (* 36 *) until_left_absorb (φ ψ : t) : φ U (φ U ψ) ≈ φ U ψ.
Proof.
  apply equiv_def; split.
  - rewrite until_right_or_order.
    now rewrite or_idem.
  - now apply until_insertion.
Qed.

Lemma (* 37 *) until_right_absorb (φ ψ : t) : (φ U ψ) U ψ ≈ φ U ψ.
Admitted.

End MinimalLinearTemporalLogic.
