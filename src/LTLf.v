Require Import
  Coq.Classes.Morphisms
  LTL.

Module Type FiniteLinearTemporalLogic.

Declare Module LTL : LinearTemporalLogic.
Include LTL.

Parameter EOF : t.
Parameter weak_next : t -> t.

Notation "'ω'" := EOF           (at level 0).
Notation "● p" := (weak_next p) (at level 0, right associativity).

Declare Instance weak_next_respects_impl : Proper (impl ==> impl) weak_next.
Program Instance weak_next_respects_eqv : Proper (eqv ==> eqv) weak_next.

Hypothesis end_def : ω ≈ ¬◯ ⊤.
Hypothesis weak_next_def : forall (φ : t), ● φ ≈ ◯ φ ∨ ω.

Lemma evn_end : ◇ ω ≈ ⊤.
Proof.
  rewrite end_def.
  rewrite next_true.
  rewrite not_true.
Abort.

Lemma next_end : ◯ ω ≈ ⊥.
Proof.
  rewrite end_def.
  rewrite next_true.
  rewrite not_true.
  now rewrite next_false.
Qed.

Lemma next_impl_not_end (φ : t) : ◯ φ ⟹ ¬ω.
Proof.
  rewrite end_def.
  rewrite next_true.
  rewrite not_not.
  apply impl_def.
  now rewrite or_true.
Qed.

Lemma weak_next_impl (φ ψ : t) : ● (φ → ψ) ≈ ● φ → ● ψ.
Proof.
  intros.
  rewrite !weak_next_def.
  rewrite next_or.
  rewrite <- or_assoc.
  rewrite not_or.
  rewrite (or_comm (¬ ◯ φ ∧ ¬ ω) (◯ ψ)).
  rewrite (or_comm (_ ∨ (_ ∧ _)) ω).
  rewrite !or_and.
  rewrite <- !(or_assoc ω (◯ ψ)).
  rewrite (or_comm ω (◯ ψ)).
  rewrite !or_assoc.
  rewrite true_def.
  rewrite or_true.
  rewrite and_true.
  rewrite <- (or_assoc (◯ ψ)).
  rewrite (or_comm _ (¬ ◯ φ)).
  now rewrite next_not.
Qed.

(* jww (2021-01-26): By end_def, ω ≈ ⊥ always. *)
Lemma end_excl_middle : (ω ≈ ⊤) \/ (ω ≈ ⊥).
Proof.
  rewrite !end_def.
  rewrite next_true.
  rewrite not_true.
  now right.
Qed.

Lemma wait_expand (φ ψ : t) : φ W ψ ≈ ψ ∨ (φ ∧ ● (φ W ψ)).
Proof.
  rewrite weak_next_def.
  rewrite law_181 at 1.
  destruct end_excl_middle.
  - rewrite H.
    rewrite or_true.
    rewrite and_true.
    rewrite or_and.
    admit.
  - rewrite H.
    now rewrite or_false.
Admitted.

Lemma weak_next_step (φ : t) : φ ≈ ⊤ -> ● φ ≈ ⊤.
Proof.
  intros.
  rewrite H.
  rewrite weak_next_def.
  destruct end_excl_middle.
  - rewrite H0.
    rewrite next_true.
    now rewrite or_idem.
  - rewrite H0.
    rewrite next_true.
    now rewrite or_false.
Qed.

Lemma weak_next_induction (φ ψ : t) : (φ ⟹ ψ) -> (φ ⟹ ● φ) -> (φ ⟹ □ ψ).
Proof.
  intros.
  rewrite law_224.
  rewrite wait_expand.
  rewrite weak_next_def in *.
  rewrite false_or.
  destruct end_excl_middle.
  - rewrite H1.
    rewrite or_true.
    now rewrite and_true.
  - rewrite H1 in *; clear H1.
    rewrite or_false in *.
    rewrite <- H; clear H.
    admit.
Abort.

End FiniteLinearTemporalLogic.
