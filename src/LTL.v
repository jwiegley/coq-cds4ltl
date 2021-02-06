Set Warnings "-local-declaration".

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

Notation "◇ p"     := (eventually p) (at level 0, right associativity).
Notation "□ p"     := (always p)     (at level 0, right associativity).
Notation "p 'W' q" := (wait p q)     (at level 44, right associativity).
Notation "p 'R' q" := (release p q) (at level 45, right associativity).
Notation "p 'M' q" := (strong_release p q) (at level 45, right associativity).

Declare Instance eventually_respects_impl : Proper (impl ==> impl) eventually.
Program Instance eventually_respects_eqv : Proper (eqv ==> eqv) eventually.
Declare Instance always_respects_impl : Proper (impl ==> impl) always.
Program Instance always_respects_eqv : Proper (eqv ==> eqv) always.
Declare Instance wait_respects_impl : Proper (impl ==> impl ==> impl) wait.
Program Instance wait_respects_eqv : Proper (eqv ==> eqv ==> eqv) wait.
Declare Instance release_respects_impl : Proper (impl ==> impl ==> impl) release.
Program Instance release_respects_eqv : Proper (eqv ==> eqv ==> eqv) release.
Declare Instance strong_release_respects_impl : Proper (impl ==> impl ==> impl) strong_release.
Program Instance strong_release_respects_eqv : Proper (eqv ==> eqv ==> eqv) strong_release.

(*** 3.3 Eventually ◇ *)

(**
(38) Deﬁnition of ◇ : ◇ q ≡ true U q
(39) Absorption of ◇ into U : p U q ∧ ◇ q ≡ p U q
(40) Absorption of U into ◇ : p U q ∨ ◇ q ≡ ◇ q
(41) Absorption of U into ◇ : p U ◇ q ≡ ◇ q
(42) Eventuality: p U q ⇒ ◇ q
(43) Truth of ◇ : ◇ true ≡ true
(44) Falsehood of ◇ : ◇ false ≡ false
(45) Expansion of ◇ : ◇ p ≡ p ∨ ◯ ◇ p
(46) Weakening of ◇ : p ⇒ ◇ p
(47) Weakening of ◇ : ◯ p ⇒ ◇ p
(48) Absorption of ∨ into ◇ : p ∨ ◇ p ≡ ◇ p
(49) Absorption of ◇ into ∧ : ◇ p ∧ p ≡ p
(50) Absorption of ◇ : ◇ ◇ p ≡ ◇ p
(51) Exchange of ◯ and ◇ : ◯ ◇ p ≡ ◇ ◯ p
(52) Distributivity of ◇ over ∨ : ◇ (p ∨ q) ≡ ◇ p ∨ ◇ q
(53) Distributivity of ◇ over ∧ : ◇ (p ∧ q) ⇒ ◇ p ∧ ◇ q
*)

Axiom (* 38 *) evn_def : forall (φ : t), ◇ φ ≈ ⊤ U φ.

Lemma (* 39 *) law_39 (φ ψ : t) : (φ U ψ) ∧ ◇ ψ ≈ φ U ψ.
Proof.
  rewrite evn_def.
  rewrite <- until_right_and.
  now rewrite and_true.
Qed.

Lemma (* 40 *) until_absorb_or_evn (φ ψ : t) : (φ U ψ) ∨ ◇ ψ ≈ ◇ ψ.
Proof.
  rewrite evn_def.
  split.
  - rewrite until_right_or.
    now rewrite or_true.
  - rewrite or_comm.
    now apply or_inj.
Qed.

Lemma (* 41 *) until_absorb_evn (φ ψ : t) : φ U ◇ ψ ≈ ◇ ψ.
Proof.
  rewrite evn_def.
  split.
  - rewrite until_right_or_order.
    now rewrite or_true.
  - now apply until_insertion.
Qed.

Lemma (* 42 *) law_42 (φ ψ : t) : φ U ψ ⟹ ◇ ψ.
Proof.
  rewrite <- (until_absorb_evn φ).
  apply until_respects_impl; [reflexivity|].
  rewrite evn_def.
  now rewrite <- until_insertion.
Qed.

Lemma (* 43 *) law_43 : ◇ ⊤ ≈ ⊤.
Proof.
  rewrite evn_def.
  now apply until_true.
Qed.

Lemma (* 44 *) law_44 : ◇ ⊥ ≈ ⊥.
Proof.
  rewrite evn_def.
  now apply until_right_bottom.
Qed.

Lemma (* 45 *) law_45 (φ : t) : ◇ φ ≈ φ ∨ ◯ ◇ φ.
Proof.
  rewrite evn_def.
  rewrite until_expansion at 1.
  now rewrite true_and.
Qed.

Lemma (* 46 *) evn_weaken (φ : t) : φ ⟹ ◇ φ.
Proof.
  rewrite evn_def.
  now rewrite <- until_insertion.
Qed.

Lemma (* 47 *) law_47 (φ : t) : ◯ φ ⟹ ◇ φ.
Proof.
  rewrite evn_def.
  rewrite until_expansion.
  rewrite or_comm.
  rewrite <- or_inj.
  rewrite true_and.
  apply next_respects_impl.
  rewrite <- evn_def.
  apply evn_weaken.
Qed.

Lemma (* 48 *) law_48 (φ : t) : φ ∨ ◇ φ ≈ ◇ φ.
Proof.
  rewrite <- (false_until φ) at 1.
  now apply until_absorb_or_evn.
Qed.

Lemma (* 49 *) law_49 (φ : t) : ◇ φ ∧ φ ≈ φ.
Proof.
  rewrite evn_def.
  now apply until_absorb_u_and.
Qed.

Lemma (* 50 *) law_50 (φ : t) : ◇ ◇ φ ≈ ◇ φ.
Proof.
  rewrite !evn_def.
  now apply until_left_absorb.
Qed.

Lemma (* 51 *) law_51 (φ : t) : ◯ ◇ φ ≈ ◇ ◯ φ.
Proof.
  rewrite !evn_def.
  rewrite next_until.
  now rewrite next_true.
Qed.

Lemma (* 52 *) evn_or (φ ψ : t) : ◇ (φ ∨ ψ) ≈ ◇ φ ∨ ◇ ψ.
Proof.
  rewrite !evn_def.
  now apply until_left_or.
Qed.

Lemma (* 53 *) law_53 (φ ψ : t) : ◇ (φ ∧ ψ) ⟹ ◇ φ ∧ ◇ ψ.
Proof.
  rewrite !evn_def.
  now apply until_left_and.
Qed.

(*** 3.4 Always □ *)

(**
(54) Definition of □ : □ p ≡ ¬◇ ¬p
(55) Axiom, U Induction : □ (p ⇒ (◯ p ∧ q) ∨ r) ⇒ (p ⇒ □ q ∨ q U r)
(56) Axiom, U Induction : □ (p ⇒ ◯ (p ∨ q)) ⇒ (p ⇒ □ p ∨ p U q)
(57) □ Induction: □ (p → ◯ p) ⇒ (p → □ p)
(58) ◇ Induction: □ (◯ p → p) ⇒ (◇ p → p)
(59) ◇ p ≡ ¬□ ¬p
(60) Dual of □ : ¬□ p ≡ ◇ ¬p
(61) Dual of ◇ : ¬◇ p ≡ □ ¬p
(62) Dual of ◇ □ : ¬◇ □ p ≡ □ ◇ ¬p
(63) Dual of □ ◇ : ¬□ ◇ p ≡ ◇ □ ¬p
(64) Truth of □ : □ true ≡ true
(65) Falsehood of □ : □ false ≡ false
(66) Expansion of □ : □ p ≡ p ∧ ◯ □ p
(67) Expansion of □ : □ p ≡ p ∧ ◯ p ∧ ◯ □ p
(68) Absorption of ∧ into □ : p ∧ □ p ≡ □ p
(69) Absorption of □ into ∨ : □ p ∨ p ≡ p
(70) Absorption of ◇ into □ : ◇ p ∧ □ p ≡ □ p
(71) Absorption of □ into ◇ : □ p ∨ ◇ p ≡ ◇ p
(72) Absorption of □ : □ □ p ≡ □ p
(73) Exchange of ◯ and □ : ◯ □ p ≡ ◯ □ p
(74) p → □ p ≡ p → ◯ □ p
(75) p ∧ ◇ ¬p ⇒ ◇ (p ∧ ◯ ¬p)
(76) Strengthening of □ : □ p ⇒ p
(77) Strengthening of □ : □ p ⇒ ◇ p
(78) Strengthening of □ : □ p ⇒ ◯ p
(79) Strengthening of □ : □ p ⇒ ◯ □
(80) ◯ generalization: □ p ⇒ □ ◯ p
(81) □ p ⇒ ¬(q U ¬p)
*)

Axiom until_continue : forall (φ ψ : t), ψ ∧ φ U ◯ ¬ψ ⟹ φ U (ψ ∧ ◯ ¬ψ).

Axiom (* 54 *) always_def : forall (φ : t), □ φ ≈ ¬◇ ¬φ.
Axiom (* 55 *) always_until_and_ind : forall (φ ψ χ : t),
  □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ φ → □ ψ ∨ ψ U χ.

Lemma (* 73 *) law_73 (φ : t) : ◯ □ φ ≈ □ ◯ φ.
Proof.
  rewrite !always_def.
  rewrite next_not.
  rewrite law_51.
  now rewrite <- next_not.
Qed.

Lemma (* 66 *) law_66 (φ : t) : □ φ ≈ φ ∧ ◯ □ φ.
Proof.
  rewrite always_def.
  rewrite law_45 at 1.
  rewrite not_or.
  rewrite not_not.
  now rewrite next_not.
Qed.

Lemma (* 56 *) always_until_or_ind : forall (φ ψ : t),
  □ (φ → ◯ (φ ∨ ψ)) ⟹ φ → □ φ ∨ φ U ψ.
Proof.
  intros.
  pose proof (always_until_and_ind φ (◯ φ) (◯ ψ)).
  rewrite and_idem in H.
  rewrite <- next_or in H.
  rewrite H; clear H.
  (* rewrite (until_expansion φ ψ). *)
  (* rewrite (law_66 φ). *)
  (* rewrite law_73. *)
  (* rewrite next_until. *)
  (* apply or_respects_impl; [reflexivity|]. *)
  (* Set Printing Parentheses. *)
  (* rewrite <- or_assoc. *)
  (* rewrite (or_comm (and _ _)). *)
  (* rewrite or_assoc. *)
  (* rewrite <- and_or. *)
  (* rewrite or_and. *)
  (* apply or_respects_impl; [reflexivity|]. *)
  rewrite <- next_until.
  rewrite <- law_73.
  rewrite <- next_or.
  rewrite law_66 at 2.
  rewrite until_expansion at 2.
  rewrite !or_and.
  rewrite <- !or_assoc.
  rewrite !or_and.
  boolean.
  rewrite <- !or_and.
  rewrite !or_assoc.
  rewrite (or_comm ψ).
  rewrite <- (or_inj _ ψ).
  rewrite !or_and.
  rewrite !(or_comm _ φ).
  rewrite <- !or_assoc.
  boolean.
  rewrite or_assoc.
  now rewrite next_or.
Qed.

Lemma (* 57 *) always_induction (φ : t) : □ (φ → ◯ φ) ⟹ (φ → □ φ).
Proof.
  pose proof (always_until_or_ind φ ⊥).
  rewrite or_false in H.
  rewrite H.
  rewrite until_right_bottom.
  now rewrite or_false.
Qed.

Lemma (* 58 *) evn_induction (φ : t) : □ (◯ φ → φ) ⟹ (◇ φ → φ).
Proof.
  rewrite !always_def.
  rewrite !evn_def.
  apply contrapositive.
  rewrite !not_or.
  rewrite (and_comm (not (not (next _)))).
  rewrite <- !next_not.
  rewrite <- until_continue.
  rewrite not_and.
  rewrite not_or.
  rewrite !not_not.
  rewrite until_expansion.
  rewrite next_until.
  rewrite and_or_r.
  boolean.
  rewrite next_true.
  now boolean.
Qed.

Lemma (* 59 *) law_59 (φ : t) : ◇ φ ≈ ¬□ ¬φ.
Proof. now rewrite always_def; boolean. Qed.

Lemma (* 60 *) law_60 (φ : t) : ¬□ φ ≈ ◇ ¬φ.
Proof. now rewrite always_def; boolean. Qed.

Lemma (* 61 *) law_61 (φ : t) : ¬◇ φ ≈ □ ¬φ.
Proof. now rewrite always_def; boolean. Qed.

Lemma (* 62 *) law_62 (φ : t) : ¬◇ □ φ ≈ □ ◇ ¬φ.
Proof. now rewrite !always_def. Qed.

Lemma (* 63 *) law_63 (φ : t) : ¬□ ◇ φ ≈ ◇ □ ¬φ.
Proof. now rewrite !always_def; boolean. Qed.

Lemma (* 64 *) law_64 : □ ⊤ ≈ ⊤.
Proof.
  rewrite always_def.
  rewrite not_true.
  rewrite law_44.
  now rewrite not_false.
Qed.

Lemma (* 65 *) law_65 : □ ⊥ ≈ ⊥.
Proof.
  rewrite always_def.
  rewrite not_false.
  rewrite law_43.
  now rewrite not_true.
Qed.

Lemma (* 66 *) law_66 (φ : t) : □ φ ≈ φ ∧ ◯ □ φ.
Proof.
  rewrite always_def.
  rewrite law_45 at 1.
  rewrite not_or.
  rewrite not_not.
  now rewrite next_not.
Qed.

Lemma (* 67 *) law_67 (φ : t) : □ φ ≈ φ ∧ ◯ φ ∧ ◯ □ φ.
Proof.
  split.
  - rewrite <- next_and.
    assert (□ φ ⟹ φ ∧ □ φ).
      rewrite law_66.
      rewrite <- and_assoc.
      now rewrite and_idem.
    rewrite <- H.
    now apply law_66.
  - rewrite <- and_assoc.
    rewrite (and_comm φ).
    rewrite and_assoc.
    rewrite <- law_66.
    rewrite and_comm.
    now apply and_proj.
Qed.

Lemma (* 68 *) law_68 (φ : t) : φ ∧ □ φ ≈ □ φ.
Proof.
  split.
  - rewrite always_def.
    rewrite and_comm.
    now apply and_proj.
  - rewrite law_66.
    rewrite <- and_assoc.
    now rewrite and_idem.
Qed.

Lemma (* 69 *) law_69 (φ : t) : □ φ ∨ φ ≈ φ.
Proof.
  split.
  - rewrite <- law_68.
    rewrite or_comm.
    rewrite or_and.
    rewrite or_idem.
    now apply and_proj.
  - rewrite or_comm.
    now apply or_inj.
Qed.

Lemma (* 70 *) law_70 (φ : t) : ◇ φ ∧ □ φ ≈ □ φ.
Proof.
  split.
  - rewrite and_comm.
    now apply and_proj.
  - rewrite <- law_68 at 1.
    now rewrite <- evn_weaken.
Qed.

Lemma (* 71 *) law_71 (φ : t) : □ φ ∨ ◇ φ ≈ ◇ φ.
Proof.
  split.
  - rewrite always_def.
    apply contrapositive.
    rewrite <- (evn_weaken (¬ φ)).
    rewrite not_not.
    now rewrite law_48.
  - rewrite or_comm.
    now apply or_inj.
Qed.

Lemma (* 72 *) law_72 (φ : t) : □ □ φ ≈ □ φ.
Proof.
  rewrite always_def.
  rewrite law_60.
  rewrite law_50.
  now rewrite <- always_def.
Qed.

Lemma (* 73 *) law_73 (φ : t) : ◯ □ φ ≈ □ ◯ φ.
Proof.
  rewrite !always_def.
  rewrite next_not.
  rewrite law_51.
  now rewrite <- next_not.
Qed.

Lemma (* 74 *) law_74 (φ : t) : φ → □ φ ⟹ φ → ◯ □ φ.
Proof.
  rewrite always_def.
  rewrite <- always_def.
  rewrite law_66 at 1.
  rewrite or_and.
  rewrite or_comm at 1.
  rewrite true_def.
  now rewrite true_and.
Qed.

Lemma (* 75 *) law_75 (φ : t) : φ ∧ ◇ ¬φ ⟹ ◇ (φ ∧ ◯ ¬φ).
Proof.
  apply contrapositive.
  rewrite !and_def.
  rewrite <- !always_def.
  rewrite next_not.
  rewrite !not_not.
  now apply always_induction.
Qed.

Lemma (* 76 *) law_76 (φ : t) : □ φ ⟹ φ.
Proof.
  rewrite always_def.
  apply contrapositive.
  rewrite not_not.
  now apply evn_weaken.
Qed.

Lemma (* NEW *) always_apply (φ ψ : t) : □ (φ → ψ) ∧ φ ⟹ □ (φ → ψ) ∧ φ ∧ ψ.
Proof.
  rewrite <- (and_idem (□ (φ → ψ) ∧ φ)).
  rewrite law_76 at 2.
  rewrite impl_apply.
  rewrite and_assoc.
  rewrite <- (and_assoc _ _ ψ).
  now rewrite and_idem.
Qed.

Lemma (* 77 *) law_77 (φ : t) : □ φ ⟹ ◇ φ.
Proof.
  rewrite <- evn_weaken.
  now apply law_76.
Qed.

Lemma (* 78 *) law_78 (φ : t) : □ φ ⟹ ◯ φ.
Proof.
  rewrite law_67.
  rewrite and_comm.
  rewrite and_proj.
  now apply and_proj.
Qed.

Lemma (* 79 *) law_79 (φ : t) : □ φ ⟹ ◯ □ φ.
Proof.
  rewrite <- law_78.
  now rewrite law_72.
Qed.

Lemma (* 80 *) law_80 (φ : t) : □ φ ⟹ □ ◯ φ.
Proof.
  rewrite <- law_73.
  now apply law_79.
Qed.

Lemma (* 81 *) law_81 (φ ψ : t) : □ φ ⟹ ¬(ψ U ¬φ).
Proof.
  rewrite always_def.
  apply contrapositive.
  rewrite !not_not.
  now rewrite law_42.
Qed.

(*** 3.5 Temporal Deduction *)

(**
(82) Temporal deduction:
     To prove □ P₁ ∧ □ P₂ ⇒ Q, assume P₁ and P₂, and prove Q.
     You cannot use textual substitution in P₁ or P₂.

This follows from the axiom impl_denote, which denotes implication (⟹) in
Coq's own logic.
 *)

Lemma (* 82 *) temporal_deduction : forall (φ ψ : t),
  (φ ≈ ⊤ -> ψ ≈ ⊤) -> □ φ ⟹ ψ.
Proof.
  intros.
  apply impl_denote; intros.
  apply H.
  destruct H0.
  rewrite law_76 in H1.
  split; auto.
  now apply impl_true.
Qed.

(*** 3.6 Always □, Continued *)

(**
(83) Distributivity of ∧ over U : □ p ∧ q U r ⇒ (p ∧ q) U (p ∧ r)
(84) U implication : □ p ∧ ◇ q ⇒ p U q
(85) Right monotonicity of U : □ (p → q) ⇒ (r U p → r U q)
(86) Left monotonicity of U : □ (p → q) ⇒ (p U r → q U r)
(87) Distributivity of ¬ over □ : □ ¬p ⇒ ¬□ p
(88) Distributivity of ◇ over ∧ : □ p ∧ ◇ q ⇒ ◇ (p ∧ q)
(89) ◇ excluded middle : ◇ p ∨ □ ¬p
(90) □ excluded middle : □ p ∨ ◇ ¬p
(91) Temporal excluded middle : ◇ p ∨ ◇ ¬p
(92) ◇ contradiction : ◇ p ∧ □ ¬p ≡ false
(93) □ contradiction : □ p ∧ ◇ ¬p ≡ false
(94) Temporal contradiction : □ p ∧ □ ¬p ≡ false
(95) □ ◇ excluded middle : □ ◇ p ∨ ◇ □ ¬p
(96) ◇ □ excluded middle : ◇ □ p ∨ □ ◇ ¬p
(97) □ ◇ contradiction : □ ◇ p ∧ ◇ □ ¬p ≡ false
(98) ◇ □ contradiction : ◇ □ p ∧ □ ◇ ¬p ≡ false
(99) Distributivity of □ over ∧ : □ (p ∧ q) ≡ □ p ∧ □ q
(100) Distributivity of □ over ∨ : □ p ∨ □ q ⇒ □ (p ∨ q)
(101) Logical equivalence law of ◯ : □ (p ≡ q) ⇒ (◯ p ≡ ◯ q)
(102) Logical equivalence law of ◇ : □ (p ≡ q) ⇒ (◇ p ≡ ◇ q)
(103) Logical equivalence law of □ : □ (p ≡ q) ⇒ (□ p ≡ □ q)
(104) Distributivity of ◇ over ⇒ : ◇ (p → q) ≡ (□ p → ◇ q)
(105) Distributivity of ◇ over ⇒ : (◇ p → ◇ q) ⇒ ◇ (p → q)
(106) ∧ frame law of ◯ : □ p ⇒ (◯ q → ◯ (p ∧ q))
(107) ∧ frame law of ◇ : □ p ⇒ (◇ q → ◇ (p ∧ q))
(108) ∧ frame law of □ : □ p ⇒ (□ q → □ (p ∧ q))
(109) ∨ frame law of ◯ : □ p ⇒ (◯ q → ◯ (p ∨ q))
(110) ∨ frame law of ◇ : □ p ⇒ (◇ q → ◇ (p ∨ q))
(111) ∨ frame law of □ : □ p ⇒ (□ q → □ (p ∨ q))
(112) ⇒ frame law of ◯ : □ p ⇒ (◯ q → ◯ (p → q))
(113) ⇒ frame law of ◇ : □ p ⇒ (◇ q → ◇ (p → q))
(114) ⇒ frame law of □ : □ p ⇒ (□ q → □ (p → q))
(115) ≡ frame law of ◯ : □ p ⇒ (◯ q → ◯ (p ≡ q))
(116) ≡ frame law of ◇ : □ p ⇒ (◇ q → ◇ (p ≡ q))
(117) ≡ frame law of □ : □ p ⇒ (□ q → □ (p ≡ q))
(118) Monotonicity of ◯ : □ (p → q) ⇒ (◯ p → ◯ q)
(119) Monotonicity of ◇ : □ (p → q) ⇒ (◇ p → ◇ q)
(120) Monotonicity of □ : □ (p → q) ⇒ (□ p → □ q)
(121) Consequence rule of ◯ : □ ((p → q) ∧ (q → ◯ r) ∧ (r → s)) ⇒ (p → ◯ s)
(122) Consequence rule of ◇ : □ ((p → q) ∧ (q → ◇ r) ∧ (r → s)) ⇒ (p → ◇ s)
(123) Consequence rule of □ : □ ((p → q) ∧ (q → □ r) ∧ (r → s)) ⇒ (p → □ s)
(124) Catenation rule of ◇ : □ ((p → ◇ q) ∧ (q → ◇ r)) ⇒ (p → ◇ r)
(125) Catenation rule of □ : □ ((p → □ q) ∧ (q → □ r)) ⇒ (p → □ r)
(126) Catenation rule of U : □ ((p → q U r) ∧ (r → q U s)) ⇒ (p → q U s)
(127) U strengthening rule: □ ((p → r) ∧ (q → s)) ⇒ (p U q → r U s)
(128) Induction rule ◇ : □ (p ∨ ◯ q → q) ⇒ (◇ p → q)
(129) Induction rule □ : □ (p → q ∧ ◯ p) ⇒ (p → □ q)
(130) Induction rule U : □ (p → ¬q ∧ ◯ p) ⇒ (p → ¬(r U q))
(131) ◇ Conﬂuence: □ ((p → ◇ (q ∨ r)) ∧ (q → ◇ t) ∧ (r → ◇ t)) ⇒ (p → ◇ t)
(132) Temporal generalization law : □ (□ p → q) ⇒ (□ p → □ q)
(133) Temporal particularization law : □ (p → ◇ q) ⇒ (◇ p → ◇ q)
(134) □ (p → ◯ q) ⇒ (p → ◇ q)
(135) □ (p → ◯ ¬p) ⇒ (p → ¬□ p)
*)

Lemma (* 83 *) (*Distributivity of ∧ over U*) law_83 (φ ψ χ : t) : □ φ ∧ ψ U χ ⟹ (φ ∧ ψ) U (φ ∧ χ).
Proof.
  apply and_impl_iff.
  apply temporal_deduction; intro H; rewrite H.
  now boolean.
Qed.

Lemma (* 84 *) (*U implication*) law_84 (φ ψ : t) : □ φ ∧ ◇ ψ ⟹ φ U ψ.
Proof.
  rewrite evn_def.
  rewrite law_83.
  rewrite and_true.
  rewrite until_left_and.
  now boolean.
Qed.

Corollary (* NEW *) law_84b (φ ψ : t) : □ φ ⟹ ◇ ψ → φ U ψ.
Proof.
  apply and_impl_iff.
  now apply law_84.
Qed.

Corollary (* NEW *) law_84c (φ ψ : t) : ¬(φ U ψ) ⟹ ◇ ψ → ◇ ¬φ.
Proof.
  apply contrapositive.
  rewrite not_or.
  rewrite !not_not.
  rewrite <- always_def.
  rewrite and_comm.
  now apply law_84.
Qed.

Lemma (* 85 *) (*Right monotonicity of U*) law_85 (φ ψ χ : t) : □ (φ → ψ) ⟹ (χ U φ → χ U ψ).
Proof.
  apply and_impl_iff.
  rewrite law_83.
  now apply until_respects_impl; boolean.
Qed.

Lemma (* 86 *) (*Left monotonicity of U*) law_86 (φ ψ χ : t) : □ (φ → ψ) ⟹ (φ U χ → ψ U χ).
Proof.
  apply and_impl_iff.
  rewrite law_83.
  now apply until_respects_impl; boolean.
Qed.

Lemma (* 87 *) (*Distributivity of ¬ over □*) law_87 (φ : t) : □ ¬φ ⟹ ¬□ φ.
Proof.
  rewrite !always_def.
  boolean.
  rewrite <- evn_weaken.
  now apply evn_weaken.
Qed.

Lemma (* 88 *) (*Distributivity of ◇ over ∧*) law_88 (φ ψ : t) : □ φ ∧ ◇ ψ ⟹ ◇ (φ ∧ ψ).
Proof.
  rewrite !evn_def.
  rewrite law_83.
  boolean.
  now apply until_respects_impl; boolean.
Qed.

Lemma (* 89 *) (*◇ excluded middle*) law_89 (φ : t) : ◇ φ ∨ □ ¬φ ≈ ⊤.
Proof.
  rewrite always_def.
  now boolean.
Qed.

Lemma (* 90 *) (*□ excluded middle*) law_90 (φ : t) : □ φ ∨ ◇ ¬φ ≈ ⊤.
Proof.
  rewrite always_def.
  now boolean.
Qed.

Lemma (* 91 *) (*Temporal excluded middle*) law_91 (φ : t) : ◇ φ ∨ ◇ ¬φ ≈ ⊤.
Proof.
  rewrite !evn_def.
  now apply until_excl_middle.
Qed.

Lemma (* 92 *) (*◇ contradiction*) law_92 (φ : t) : ◇ φ ∧ □ ¬φ ≈ ⊥.
Proof.
  rewrite always_def.
  now boolean.
Qed.

Lemma (* 93 *) (*□ contradiction*) law_93 (φ : t) : □ φ ∧ ◇ ¬φ ≈ ⊥.
Proof.
  rewrite always_def.
  now boolean.
Qed.

Lemma (* 94 *) (*Temporal contradiction*) law_94 (φ : t) : □ φ ∧ □ ¬φ ≈ ⊥.
Proof.
  rewrite <- law_61.
  rewrite always_def.
  rewrite <- not_not.
  rewrite not_and.
  rewrite !not_not.
  rewrite <- evn_or.
  boolean.
  rewrite law_43.
  now boolean.
Qed.

Lemma (* 95 *) (*□ ◇ excluded middle*) law_95 (φ : t) : □ ◇ φ ∨ ◇ □ ¬φ ≈ ⊤.
Proof.
  rewrite <- law_63.
  now boolean.
Qed.

Lemma (* 96 *) (*◇ □ excluded middle*) law_96 (φ : t) : ◇ □ φ ∨ □ ◇ ¬φ ≈ ⊤.
Proof.
  rewrite <- law_62.
  now boolean.
Qed.

Lemma (* 97 *) (*□ ◇ contradiction*) law_97 (φ : t) : □ ◇ φ ∧ ◇ □ ¬φ ≈ ⊥.
Proof.
  rewrite <- law_63.
  now boolean.
Qed.

Lemma (* 98 *) (*◇ □ contradiction*) law_98 (φ : t) : ◇ □ φ ∧ □ ◇ ¬φ ≈ ⊥.
Proof.
  rewrite <- law_62.
  now boolean.
Qed.

Lemma (* 99 *) (*Distributivity of □ over ∧*) law_99 (φ ψ : t) : □ (φ ∧ ψ) ≈ □ φ ∧ □ ψ.
Proof.
  rewrite !always_def.
  rewrite not_and.
  rewrite evn_or.
  now rewrite not_or.
Qed.

Lemma (* 100 *) (*Distributivity of □ over ∨*) law_100 (φ ψ : t) : □ φ ∨ □ ψ ⟹ □ (φ ∨ ψ).
Proof.
  rewrite !always_def.
  apply contrapositive.
  rewrite not_or.
  rewrite !not_not.
  rewrite law_53.
  now rewrite <- and_def.
Qed.

Lemma (* 101 *) (*Logical equivalence law of ◯*) law_101 (φ ψ : t) : □ (φ ≡ ψ) ⟹ (◯ φ ≡ ◯ ψ).
Proof.
  boolean.
  rewrite (or_comm _ φ).
  rewrite (or_comm _ (◯ φ)).
  rewrite <- !or_assoc.
  now boolean.
Qed.

Lemma (* 102 *) (*Logical equivalence law of ◇*) law_102 (φ ψ : t) : □ (φ ≡ ψ) ⟹ (◇ φ ≡ ◇ ψ).
Proof.
  boolean.
  rewrite (or_comm _ φ).
  rewrite (or_comm _ (◇ φ)).
  rewrite <- !or_assoc.
  now boolean.
Qed.

Lemma (* 103 *) (*Logical equivalence law of □*) law_103 (φ ψ : t) : □ (φ ≡ ψ) ⟹ (□ φ ≡ □ ψ).
Proof.
  boolean.
  rewrite (or_comm _ φ).
  rewrite (or_comm _ (□ φ)).
  rewrite <- !or_assoc.
  now boolean.
Qed.

Lemma (* 104 *) (*Distributivity of ◇ over ⟹*) law_104 (φ ψ : t) : ◇ (φ → ψ) ≈ (□ φ → ◇ ψ).
Proof.
  rewrite evn_or.
  now rewrite law_60.
Qed.

Lemma (* 105 *) (*Distributivity of ◇ over ⟹*) law_105 (φ ψ : t) : (◇ φ → ◇ ψ) ⟹ ◇ (φ → ψ).
Proof.
  rewrite evn_or.
  rewrite <- law_60.
  rewrite law_61.
  now rewrite law_87.
Qed.

Lemma (* 106 *) (*∧ frame law of ◯*) law_106 (φ ψ : t) : □ φ ⟹ (◯ ψ → ◯ (φ ∧ ψ)).
Proof.
  apply and_impl_iff.
  rewrite law_78.
  now rewrite next_and.
Qed.

Lemma (* 107 *) (*∧ frame law of ◇*) law_107 (φ ψ : t) : □ φ ⟹ (◇ ψ → ◇ (φ ∧ ψ)).
Proof.
  apply and_impl_iff.
  now rewrite law_88.
Qed.

Lemma (* 108 *) (*∧ frame law of □*) law_108 (φ ψ : t) : □ φ ⟹ (□ ψ → □ (φ ∧ ψ)).
Proof.
  apply and_impl_iff.
  now rewrite law_99.
Qed.

Lemma (* 109 *) (*∨ frame law of ◯*) law_109 (φ ψ : t) : □ φ ⟹ (◯ ψ → ◯ (φ ∨ ψ)).
Proof.
  apply and_impl_iff.
  rewrite law_78.
  rewrite next_or.
  now rewrite and_proj, <- or_inj.
Qed.

Lemma (* 110 *) (*∨ frame law of ◇*) law_110 (φ ψ : t) : □ φ ⟹ (◇ ψ → ◇ (φ ∨ ψ)).
Proof.
  apply and_impl_iff.
  rewrite law_88.
  rewrite law_53.
  rewrite evn_or.
  now rewrite and_proj, <- or_inj.
Qed.

Lemma (* 111 *) (*∨ frame law of □*) law_111 (φ ψ : t) : □ φ ⟹ (□ ψ → □ (φ ∨ ψ)).
Proof.
  apply and_impl_iff.
  rewrite <- law_100.
  now rewrite and_proj, <- or_inj.
Qed.

Lemma (* 112 *) (*⟹ frame law of ◯*) law_112 (φ ψ : t) : □ φ ⟹ (◯ ψ → ◯ (φ → ψ)).
Proof.
  apply and_impl_iff.
  rewrite law_78.
  rewrite next_or.
  now rewrite and_comm, and_proj, or_comm, <- or_inj.
Qed.

Lemma (* 113 *) (*⟹ frame law of ◇*) law_113 (φ ψ : t) : □ φ ⟹ (◇ ψ → ◇ (φ → ψ)).
Proof.
  apply and_impl_iff.
  rewrite law_88.
  rewrite law_53.
  rewrite evn_or.
  now rewrite and_comm, and_proj, or_comm, <- or_inj.
Qed.

Lemma (* 114 *) (*⟹ frame law of □*) law_114 (φ ψ : t) : □ φ ⟹ (□ ψ → □ (φ → ψ)).
Proof.
  apply and_impl_iff.
  rewrite <- law_100.
  now rewrite and_comm, and_proj, or_comm, <- or_inj.
Qed.

Lemma (* 115 *) (*≡ frame law of ◯*) law_115 (φ ψ : t) : □ φ ⟹ (◯ ψ → ◯ (φ ≡ ψ)).
Proof.
  apply and_impl_iff.
  rewrite law_78.
  rewrite !next_or.
  boolean.
  now rewrite and_proj, (or_comm _ (_ φ)), or_comm, <- !or_inj.
Qed.

Lemma (* 116 *) (*≡ frame law of ◇*) law_116 (φ ψ : t) : □ φ ⟹ (◇ ψ → ◇ (φ ≡ ψ)).
Proof.
  apply and_impl_iff.
  rewrite law_88.
  rewrite law_53.
  rewrite !evn_or.
  boolean.
  now rewrite and_proj, (or_comm _ (_ φ)), or_comm, <- !or_inj.
Qed.

Lemma (* 117 *) (*≡ frame law of □*) law_117 (φ ψ : t) : □ φ ⟹ (□ ψ → □ (φ ≡ ψ)).
Proof.
  apply and_impl_iff.
  rewrite <- !law_100.
  boolean.
  now rewrite and_proj, (or_comm _ (_ φ)), or_comm, <- !or_inj.
Qed.

Lemma (* 118 *) (*Monotonicity of ◯*) law_118 (φ ψ : t) : □ (φ → ψ) ⟹ (◯ φ → ◯ ψ).
Proof.
  apply and_impl_iff.
  rewrite law_78.
  rewrite !next_or.
  rewrite and_comm.
  rewrite and_or.
  rewrite next_not.
  now boolean.
Qed.

Lemma (* 119 *) (*Monotonicity of ◇*) law_119 (φ ψ : t) : □ (φ → ψ) ⟹ (◇ φ → ◇ ψ).
Proof.
  apply and_impl_iff.
  rewrite law_88.
  boolean.
  rewrite law_53.
  now boolean.
Qed.

Lemma (* 120 *) (*Monotonicity of □*) law_120 (φ ψ : t) : □ (φ → ψ) ⟹ (□ φ → □ ψ).
Proof.
  apply and_impl_iff.
  rewrite <- law_99.
  boolean.
  rewrite law_99.
  now boolean.
Qed.

Lemma (* 121 *) (*Consequence rule of ◯*) law_121 (φ ψ χ ρ : t) : □ ((φ → ψ) ∧ (ψ → ◯ χ) ∧ (χ → ρ)) ⟹ (φ → ◯ ρ).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite law_76.
  rewrite <- and_assoc.
  rewrite impl_trans.
  rewrite law_118.
  now rewrite impl_trans.
Qed.

Lemma (* 122 *) (*Consequence rule of ◇*) law_122 (φ ψ χ ρ : t) : □ ((φ → ψ) ∧ (ψ → ◇ χ) ∧ (χ → ρ)) ⟹ (φ → ◇ ρ).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite law_76.
  rewrite <- and_assoc.
  rewrite impl_trans.
  rewrite law_119.
  now rewrite impl_trans.
Qed.

Lemma (* 123 *) (*Consequence rule of □*) law_123 (φ ψ χ ρ : t) : □ ((φ → ψ) ∧ (ψ → □ χ) ∧ (χ → ρ)) ⟹ (φ → □ ρ).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite law_76.
  rewrite <- and_assoc.
  rewrite impl_trans.
  rewrite law_120.
  now rewrite impl_trans.
Qed.

Lemma (* 124 *) (*Catenation rule of ◇*) law_124 (φ ψ χ : t) : □ ((φ → ◇ ψ) ∧ (ψ → ◇ χ)) ⟹ (φ → ◇ χ).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite law_119.
  rewrite impl_trans.
  now rewrite law_50.
Qed.

Lemma (* 125 *) (*Catenation rule of □*) law_125 (φ ψ χ : t) : □ ((φ → □ ψ) ∧ (ψ → □ χ)) ⟹ (φ → □ χ).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite law_120.
  rewrite impl_trans.
  now rewrite law_72.
Qed.

Lemma (* 126 *) (*Catenation rule of U*) law_126 (φ ψ χ ρ : t) : □ ((φ → ψ U χ) ∧ (χ → ψ U ρ)) ⟹ (φ → ψ U ρ).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite (law_85 _ _ ψ).
  rewrite impl_trans.
  now rewrite until_left_absorb.
Qed.

Lemma (* 127 *) (*U strengthening rule*) law_127 (φ ψ χ ρ : t) : □ ((φ → χ) ∧ (ψ → ρ)) ⟹ (φ U ψ → χ U ρ).
Proof.
  rewrite !law_99.
  rewrite (law_86 _ _ ψ).
  rewrite (law_85 _ _ χ).
  now rewrite impl_trans.
Qed.

Lemma (* 128 *) (*Induction rule ◇*) law_128 (φ ψ : t) : □ (φ ∨ ◯ ψ → ψ) ⟹ (◇ φ → ψ).
Proof.
  rewrite or_impl.
  rewrite law_99.
  rewrite evn_induction.
  rewrite law_119.
  now apply impl_trans.
Qed.

Lemma (* 129 *) (*Induction rule □*) law_129 (φ ψ : t) : □ (φ → ψ ∧ ◯ φ) ⟹ (φ → □ ψ).
Proof.
  pose proof (always_until_and_ind φ ψ ⊥).
  rewrite until_right_bottom in H.
  rewrite !or_false in H.
  now rewrite and_comm.
Qed.

Lemma (* 130 *) (*Induction rule U*) law_130 (φ ψ χ : t) : □ (φ → ¬ψ ∧ ◯ φ) ⟹ (φ → ¬(χ U ψ)).
Proof.
  rewrite law_129.
  rewrite (law_81 (¬ ψ) χ).
  now rewrite not_not.
Qed.

Lemma (* 131 *) (*◇ Conﬂuence*) law_131 (φ ψ χ ρ : t) : □ ((φ → ◇ (ψ ∨ χ)) ∧ (ψ → ◇ ρ) ∧ (χ → ◇ ρ)) ⟹ (φ → ◇ ρ).
Proof.
  pose proof (law_124 φ (ψ ∨ χ) ρ).
  rewrite !law_99 in *.
  apply (proj1 (and_impl_iff _ _ _)) in H.
  apply (proj2 (and_impl_iff _ _ _)).
  rewrite H; clear H.
  apply or_respects_impl; [|reflexivity].
  rewrite <- law_99.
  rewrite !(or_comm _ (◇ ρ)).
  rewrite <- or_and.
  apply not_respects_impl; unfold Basics.flip.
  apply always_respects_impl.
  apply or_respects_impl; [reflexivity|].
  rewrite and_def.
  now boolean.
Qed.

Lemma (* 132 *) (*Temporal generalization law*) law_132 (φ ψ : t) : □ (□ φ → ψ) ⟹ (□ φ → □ ψ).
Proof.
  apply and_impl_iff.
  rewrite <- (law_72 φ) at 2.
  rewrite <- law_99.
  boolean.
  rewrite law_99.
  now boolean.
Qed.

Lemma (* 133 *) (*Temporal particularization law*) law_133 (φ ψ : t) : □ (φ → ◇ ψ) ⟹ (◇ φ → ◇ ψ).
Proof.
  apply and_impl_iff.
  rewrite law_88.
  boolean.
  rewrite law_53.
  rewrite law_50.
  now boolean.
Qed.

Lemma (* 134 *) law_134 (φ ψ : t) : □ (φ → ◯ ψ) ⟹ (φ → ◇ ψ).
Proof.
  apply and_impl_iff.
  rewrite (evn_weaken φ) at 2.
  rewrite law_88.
  boolean.
  rewrite law_53.
  rewrite and_comm, and_proj.
  rewrite (law_45 ψ).
  rewrite or_comm, <- or_inj.
  now rewrite law_51.
Qed.

Lemma (* 135 *) law_135 (φ : t) : □ (φ → ◯ ¬φ) ⟹ (φ → ¬□ φ).
Proof.
  apply and_impl_iff.
  rewrite and_proj.
  rewrite next_not.
  rewrite <- (not_not (or _ _)).
  rewrite <- and_def.
  rewrite law_87.
  apply contrapositive.
  rewrite !not_not.
  rewrite law_99.
  rewrite <- law_80.
  now boolean.
Qed.

(*** 3.7 Proof Metatheorems *)

(**
(136) Metatheorem: P is a theorem iff □ P is a theorem.
(137) Metatheorem ◯ : If P ⇒ Q is a theorem then ◯ P ⇒ ◯ Q is a theorem.
(138) Metatheorem ◇ : If P ⇒ Q is a theorem then ◇ P ⇒ ◇ Q is a theorem.
(139) Metatheorem □ : If P ⇒ Q is a theorem then □ P ⇒ □ Q is a theorem.
*)

Lemma (* 137 *) next_metatheorem (φ ψ : t) : φ ⟹ ψ -> ◯ φ ⟹ ◯ ψ.
Proof. now apply next_respects_impl. Qed.

Lemma (* 138 *) eventually_metatheorem (φ ψ : t) : φ ⟹ ψ -> ◇ φ ⟹ ◇ ψ.
Proof. now apply eventually_respects_impl. Qed.

Lemma (* 139 *) always_metatheorem (φ ψ : t) : φ ⟹ ψ -> □ φ ⟹ □ ψ.
Proof. now apply always_respects_impl. Qed.

(*** 3.8 Always □, Continued *)

(**
(140) U □ implication: p U □ q ⇒ □ (p U q)
(141) Absorption of U into □ : p U □ p ≡ □ p
(142) Right ∧ U strengthening : p U (q ∧ r) ⇒ p U (q U r)
(143) Left ∧ U strengthening : (p ∧ q) U r ⇒ (p U q) U r
(144) Left ∧ U ordering : (p ∧ q) U r ⇒ p U (q U r)
(145) ◇ □ implication : ◇ □ p ⇒ □ ◇ p
(146) □ ◇ excluded middle : □ ◇ p ∨ □ ◇ ¬p
(147) ◇ □ contradiction : ◇ □ p ∧ ◇ □ ¬p ≡ false
(148) U frame law of ◯ : □ p ⇒ (◯ q → ◯ (p U q))
(149) U frame law of ◇ : □ p ⇒ (◇ q → ◇ (p U q))
(150) U frame law of □ : □ p ⇒ (□ q → □ (p U q))
(151) Absorption of ◇ into □ ◇ : ◇ □ ◇ p ≡ □ ◇ p
(152) Absorption of □ into ◇ □ : □ ◇ □ p ≡ ◇ □ p
(153) Absorption of □ ◇ : □ ◇ □ ◇ p ≡ □ ◇ p
(154) Absorption of ◇ □ : ◇ □ ◇ □ p ≡ ◇ □ p
(155) Absorption of ◯ into □ ◇ : ◯ □ ◇ p ≡ □ ◇ p
(156) Absorption of ◯ into ◇ □ : ◯ ◇ □ p ≡ ◇ □ p
(157) Monotonicity of □ ◇ : □ (p → q) ⇒ (□ ◇ p → □ ◇ q)
(158) Monotonicity of ◇ □ : □ (p → q) ⇒ (◇ □ p → ◇ □ q)
(159) Distributivity of □ ◇ over ∧ : □ ◇ (p ∧ q) ⇒ □ ◇ p ∧ □ ◇ q
(160) Distributivity of ◇ □ over ∨ : ◇ □ p ∨ ◇ □ q ⇒ ◇ □ (p ∨ q)
(161) Distributivity of □ ◇ over ∨ : □ ◇ (p ∨ q) ≡ □ ◇ p ∨ □ ◇ q
(162) Distributivity of ◇ □ over ∧ : ◇ □ (p ∧ q) ≡ ◇ □ p ∧ ◇ □ q
(163) Eventual latching : ◇ □ (p → □ q) ≡ ◇ □ ¬p ∨ ◇ □ q
(164) □ (□ ◇ p → ◇ q) ≡ ◇ □ ¬p ∨ □ ◇ q
(165) □ ((p ∨ □ q) ∧ (□ p ∨ q)) ≡ □ p ∨ □ q
(166) ◇ □ p ∧ □ ◇ q ⇒ □ ◇ (p ∧ q)
(167) □ ((□ p → ◇ q) ∧ (q → ◯ r)) ⇒ (□ p → ◯ □ ◇ r)
(168) Progress proof rule : □ p ∧ □ (□ p → ◇ q) ⇒ ◇ q
*)

Lemma (* 140 *) law_140 (*U □ implication*) (φ ψ : t) : φ U □ ψ ⟹ □ (φ U ψ).
Proof.
  assert (A : □ (φ U □ ψ → φ U ψ) ≈ ⊤).
    apply true_impl.
    rewrite <- (law_85 (□ ψ) ψ φ).
    pose proof (law_76 ψ).
    apply impl_def in H.
    rewrite <- H.
    now rewrite !law_64.
  assert (B : □ (φ U □ ψ → ◯ (φ U □ ψ)) ≈ ⊤).
    rewrite next_until.
    rewrite <- (until_absorb_u_or (◯ φ)).
    rewrite (or_comm _ (◯ □ ψ)).
    rewrite <- next_until.
    apply true_impl.
    pose proof (and_proj (◯ □ ψ ∨ ◯ (φ U □ ψ)) (ψ ∨ ◯ (φ U □ ψ))).
    rewrite <- H.
    rewrite (and_comm _ (ψ ∨ ◯ (φ U □ ψ))).
    rewrite <- or_and_r.
    rewrite <- law_66.
    pose proof (and_proj (□ ψ ∨ ◯ (φ U □ ψ)) (□ ψ ∨ φ)).
    rewrite <- H0.
    rewrite and_comm.
    rewrite <- or_and.
    rewrite <- until_expansion.
    boolean.
    now rewrite law_64.
  pose proof (law_129 (φ U □ ψ) (φ U ψ)).
  apply impl_def.
  rewrite <- H.
  rewrite impl_and.
  rewrite law_99.
  rewrite A.
  rewrite B.
  now boolean.
Qed.

Lemma (* 141 *) law_141 (*Absorption of U into □*) (φ : t) : φ U □ φ ≈ □ φ.
Proof.
  split.
  - rewrite law_140.
    now rewrite until_idem.
  - now apply until_insertion.
Qed.

Lemma (* 142 *) law_142 (*Right ∧ U strengthening*) (φ ψ χ : t) : φ U (ψ ∧ χ) ⟹ φ U (ψ U χ).
Proof.
  pose proof (law_85 (ψ ∧ χ) (ψ U χ) φ).
  apply impl_def.
  rewrite <- H.
  rewrite <- until_30.
  boolean.
  now apply law_64.
Qed.

Lemma (* 143 *) law_143 (*Left ∧ U strengthening*) (φ ψ χ : t) : (φ ∧ ψ) U χ ⟹ (φ U ψ) U χ.
Proof.
  pose proof (law_86 (φ ∧ ψ) (φ U ψ)).
  apply impl_def.
  rewrite <- H.
  rewrite <- until_30.
  boolean.
  now apply law_64.
Qed.

Lemma (* 144 *) law_144 (*Left ∧ U ordering*) (φ ψ χ : t) : (φ ∧ ψ) U χ ⟹ φ U (ψ U χ).
Proof.
  apply impl_def.
  rewrite <- law_127.
  rewrite <- (proj1 (impl_def _ _) (and_proj φ ψ)).
  rewrite <- until_insertion.
  boolean.
  now apply law_64.
Qed.

Lemma (* 145 *) law_145 (*◇ □ implication*) (φ : t) : ◇ □ φ ⟹ □ ◇ φ.
Proof.
  rewrite evn_def.
  rewrite law_140.
  now rewrite <- evn_def.
Qed.

Lemma (* 146 *) law_146 (*□ ◇ excluded middle*) (φ : t) : □ ◇ φ ∨ □ ◇ ¬φ ≈ ⊤.
Proof.
  rewrite <- law_62.
  apply true_impl.
  rewrite <- law_145.
  now boolean.
Qed.

Lemma (* 147 *) law_147 (*◇ □ contradiction*) (φ : t) : ◇ □ φ ∧ ◇ □ ¬φ ≈ ⊥.
Proof.
  apply not_inj.
  rewrite not_and.
  rewrite law_62.
  rewrite <- law_63.
  rewrite not_not.
  rewrite not_false.
  rewrite or_comm.
  now apply law_146.
Qed.

Lemma (* 148 *) law_148 (*U frame law of ◯*) (φ ψ : t) : □ φ ⟹ (◯ ψ → ◯ (φ U ψ)).
Proof.
  rewrite <- next_impl.
  rewrite <- until_insertion.
  boolean.
  rewrite next_true.
  now apply impl_true.
Qed.

Lemma (* 149 *) law_149 (*U frame law of ◇*) (φ ψ : t) : □ φ ⟹ (◇ ψ → ◇ (φ U ψ)).
Proof.
  apply and_impl_iff.
  rewrite law_84.
  now apply evn_weaken.
Qed.

Lemma (* 150 *) law_150 (*U frame law of □*) (φ ψ : t) : □ φ ⟹ (□ ψ → □ (φ U ψ)).
Proof.
  apply and_impl_iff.
  rewrite and_comm.
  rewrite and_proj.
  now rewrite <- until_insertion.
Qed.

Lemma (* 151 *) law_151 (*Absorption of ◇ into □ ◇*) (φ : t) : ◇ □ ◇ φ ≈ □ ◇ φ.
Proof.
  split.
  - rewrite law_145.
    now rewrite law_50.
  - now rewrite evn_weaken at 1.
Qed.

Lemma (* 152 *) law_152 (*Absorption of □ into ◇ □*) (φ : t) : □ ◇ □ φ ≈ ◇ □ φ.
Proof.
  rewrite <- (not_not φ) at 1.
  rewrite <- law_63.
  rewrite <- law_61.
  rewrite law_151.
  rewrite <- law_62.
  now boolean.
Qed.

Lemma (* 153 *) law_153 (*Absorption of □ ◇*) (φ : t) : □ ◇ □ ◇ φ ≈ □ ◇ φ.
Proof.
  rewrite law_152.
  now rewrite law_151.
Qed.

Lemma (* 154 *) law_154 (*Absorption of ◇ □*) (φ : t) : ◇ □ ◇ □ φ ≈ ◇ □ φ.
Proof.
  rewrite law_151.
  now rewrite law_152.
Qed.

Lemma (* 155 *) law_155 (*Absorption of ◯ into □ ◇*) (φ : t) : ◯ □ ◇ φ ≈ □ ◇ φ.
Proof.
  split.
  - rewrite (law_47 (□ ◇ φ)).
    now rewrite law_151.
  - now apply law_79.
Qed.

Lemma (* 156 *) law_156 (*Absorption of ◯ into ◇ □*) (φ : t) : ◯ ◇ □ φ ≈ ◇ □ φ.
Proof.
  split.
  - rewrite law_47.
    now rewrite law_50.
  - rewrite <- (law_78 (◇ □ φ)) at 1.
    now rewrite law_152.
Qed.

Lemma (* 157 *) law_157 (*Monotonicity of □ ◇*) (φ ψ : t) : □ (φ → ψ) ⟹ (□ ◇ φ → □ ◇ ψ).
Proof.
  transitivity (□ (◇ φ → ◇ ψ)).
    rewrite <- law_72.
    apply always_metatheorem.
    now rewrite law_119.
  now rewrite law_120.
Qed.

Lemma (* 158 *) law_158 (*Monotonicity of ◇ □*) (φ ψ : t) : □ (φ → ψ) ⟹ (◇ □ φ → ◇ □ ψ).
Proof.
  transitivity (□ (□ φ → □ ψ)).
    rewrite <- law_72.
    apply always_metatheorem.
    now rewrite law_120.
  now rewrite law_119.
Qed.

Lemma (* 159 *) law_159 (*Distributivity of □ ◇ over ∧*) (φ ψ : t) : □ ◇ (φ ∧ ψ) ⟹ □ ◇ φ ∧ □ ◇ ψ.
Proof.
  rewrite law_53.
  now rewrite law_99.
Qed.

Lemma (* 160 *) law_160 (*Distributivity of ◇ □ over ∨*) (φ ψ : t) : ◇ □ φ ∨ ◇ □ ψ ⟹ ◇ □ (φ ∨ ψ).
Proof.
  rewrite <- evn_or.
  now rewrite law_100.
Qed.

Lemma (* 161 *) law_161 (*Distributivity of □ ◇ over ∨*) (φ ψ : t) : □ ◇ (φ ∨ ψ) ≈ □ ◇ φ ∨ □ ◇ ψ.
Proof.
Proof.
  split.
  - assert (A : ◇ (◇ (φ ∨ ψ) ∧ □ ¬φ) ⟹ ◇ ψ).
      rewrite <- (and_proj (◇ ψ) (◇ ¬φ)).
      rewrite (and_comm (◇ ψ)).
      rewrite <- law_53.
      rewrite <- (law_50 (¬ φ ∧ ψ)).
      rewrite and_comm.
      apply eventually_metatheorem.
      rewrite <- (and_absorb (¬φ) ψ) at 2.
      rewrite law_88.
      rewrite and_or.
      now boolean.
    pose proof (law_88 (◇ (φ ∨ ψ)) (□ ¬φ)).
    rewrite A in H.
    apply always_metatheorem in H.
    rewrite law_99 in H.
    rewrite law_72 in H.
    rewrite law_152 in H.
    apply and_impl_iff in H.
    rewrite <- law_63 in H.
    rewrite not_not in H.
    now apply H.
  - rewrite evn_or.
    now rewrite law_100.
Qed.

Lemma (* 162 *) law_162 (*Distributivity of ◇ □ over ∧*) (φ ψ : t) : ◇ □ (φ ∧ ψ) ≈ ◇ □ φ ∧ ◇ □ ψ.
Proof.
  rewrite <- (not_not φ) at 1.
  rewrite <- (not_not ψ) at 1.
  rewrite <- not_or.
  rewrite <- law_63.
  rewrite law_161.
  rewrite <- !law_62.
  rewrite not_or.
  now boolean.
Qed.

Lemma (* 163 *) law_163 (*Eventual latching*) (φ ψ : t) : ◇ □ (φ → □ ψ) ≈ ◇ □ ¬φ ∨ ◇ □ ψ.
Proof.
  assert (A : ◇ □ (φ → □ ψ) ⟹ ◇ (□ ◇ φ → ◇ □ ψ)). {
    rewrite <- (evn_weaken (□ ◇ φ → ◇ □ ψ)).
    rewrite <- (law_50 (□ ψ)).
    rewrite <- law_104.
    rewrite <- (law_76 (◇ (◇ φ → ◇ □ ψ))).
    rewrite <- law_152.
    apply impl_def.
    rewrite <- law_157.
    rewrite <- law_119.
    boolean.
    now rewrite law_64.
  }
  split.
  - rewrite A.
    rewrite law_104.
    rewrite law_72.
    rewrite law_50.
    now rewrite law_63.
  - rewrite <- (law_72 ψ) at 1.
    now rewrite law_160.
Qed.

Lemma (* 164 *) law_164 (**) (φ ψ : t) : □ (□ ◇ φ → ◇ ψ) ≈ ◇ □ ¬φ ∨ □ ◇ ψ.
Proof.
  split.
  - rewrite law_120.
    rewrite law_72.
    now rewrite law_63.
  - rewrite <- law_100.
    rewrite law_63.
    now rewrite <- law_152 at 1.
Qed.

Lemma (* 165 *) law_165 (**) (φ ψ : t) : □ ((φ ∨ □ ψ) ∧ (□ φ ∨ ψ)) ≈ □ φ ∨ □ ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 166 *) law_166 (**) (φ ψ : t) : ◇ □ φ ∧ □ ◇ ψ ⟹ □ ◇ (φ ∧ ψ).
Proof.
  apply and_impl_iff.
  rewrite <- (law_72 (◇ ψ)).
  rewrite <- (law_151 (φ ∧ ψ)).
  rewrite <- law_104.
  apply eventually_metatheorem.
  apply and_impl_iff.
  rewrite <- law_72.
  rewrite <- law_99.
  now rewrite law_88.
Qed.

Lemma (* 167 *) law_167 (**) (φ ψ χ : t) : □ ((□ φ → ◇ ψ) ∧ (ψ → ◯ χ)) ⟹ (□ φ → ◯ □ ◇ χ).
Proof.
  apply and_impl_iff.
  rewrite law_99.
  rewrite (evn_weaken (□ φ)) at 2.
  rewrite law_157.
  rewrite law_152.
  rewrite (and_comm _ (always _)).
  rewrite and_assoc.
  rewrite impl_apply.
  rewrite law_50.
  rewrite (and_comm _ (always _)).
  rewrite <- and_assoc.
  rewrite and_proj.
  rewrite law_157.
  rewrite impl_apply.
  rewrite <- law_51.
  rewrite <- law_73.
  now boolean.
Qed.

Lemma (* 168 *) law_168 (*Progress proof rule*) (φ ψ : t) : ◇ □ φ ∧ □ (□ φ → ◇ ψ) ⟹ ◇ ψ.
Proof.
  rewrite law_119.
  rewrite law_50.
  rewrite and_comm.
  rewrite impl_apply.
  now boolean.
Qed.

(*** 3.9 Wait W *)

(*
(169) Deﬁnition of W : p W q ≡ □ p ∨ p U q
(170) Axiom, Distributivity of ¬ over W : ¬(p W q) ≡ ¬q U (¬p ∧ ¬q)
(171) U in terms of W : p U q ≡ p W q ∧ ◇ q
(172) p W q ≡ □ (p ∧ ¬q) ∨ p U q
(173) Distributivity of ¬ over U : ¬(p U q) ≡ ¬q W (¬p ∧ ¬q)
(174) U implication: p U q ⇒ p W q
(175) Distributivity of ∧ over W : □ p ∧ q W r ⇒ (p ∧ q) W (p ∧ r)
(176) W ◇ equivalence: p W ◇ q ≡ □ p ∨ ◇ q
(177) W □ implication: p W □ q ⇒ □ (p W q)
(178) Absorption of W into □ : p W □ p ≡ □ p
(179) Perpetuity: □ p ⇒ p W q
(180) Distributivity of ◯ over W : ◯ (p W q) ≡ ◯ p W ◯ q
(181) Expansion of W : p W q ≡ q ∨ (p ∧ ◯ (p W q))
(182) W excluded middle: p W q ∨ p W ¬q
(183) Left zero of W : true W q ≡ true
(184) Left distributivity of W over ∨ : p W (q ∨ r) ≡ p W q ∨ p W r
(185) Right distributivity of W over ∨ : p W r ∨ q W r ⇒ (p ∨ q) W r
(186) Left distributivity of W over ∧ : p W (q ∧ r) ⇒ p W q ∧ p W r
(187) Right distributivity of W over ∧ : (p ∧ q) W r ≡ p W r ∧ q W r
(188) Right distributivity of W over ⇒ : (p → q) W r ⇒ (p W r → q W r)
(189) Disjunction rule of W : p W q ≡ (p ∨ q) W q
(190) Disjunction rule of U : p U q ≡ (p ∨ q) U q
(191) Rule of W : ¬q W q
(192) Rule of U : ¬q U q ≡ ◇ q
(193) (p ⇒ q) W p
(194) ◇ p ⇒ (p → q) U p
(195) Conjunction rule of W : p W q ≡ (p ∧ ¬q) W q
(196) Conjunction rule of U : p U q ≡ (p ∧ ¬q) U q
(197) Distributivity of ¬ over W : ¬(p W q) ≡ (p ∧ ¬q) U (¬p ∧ ¬q)
(198) Distributivity of ¬ over U : ¬(p U q) ≡ (p ∧ ¬q) W (¬p ∧ ¬q)
(199) Dual of U : ¬(¬p U ¬q) ≡ q W (p ∧ q)
(200) Dual of U : ¬(¬p U ¬q) ≡ (¬p ∧ q) W (p ∧ q)
(201) Dual of W : ¬(¬p W ¬q) ≡ q U (p ∧ q)
(202) Dual of W : ¬(¬p W ¬q) ≡ (¬p ∧ q) U (p ∧ q)
(203) Idempotency of W : p W p ≡ p
(204) Right zero of W : p W true ≡ true
(205) Left identity of W : false W q ≡ q
(206) p W q ⇒ p ∨ q
(207) □ (p ∨ q) ⇒ p W q
(208) □ (¬q → p) ⇒ p W q
(209) W insertion: q ⇒ p W q
(210) W frame law of ◯ : □ p ⇒ (◯ q → ◯ (p W q))
(211) W frame law of ◇ : □ p ⇒ (◇ q → ◇ (p W q))
(212) W frame law of □ : □ p ⇒ (□ q → □ (p W q))
(213) W induction: □ (p → (◯ p ∧ q) ∨ r) ⇒ (p → q W r)
(214) W induction: □ (p → ◯ (p ∨ q)) ⇒ (p → p W q)
(215) W induction: □ (p → ◯ p) ⇒ (p → p W q)
(216) W induction: □ (p → q ∧ ◯ p) ⇒ (p → p W q)
(217) Absorption: p ∨ p W q ≡ p ∨ q
(218) Absorption: p W q ∨ q ≡ p W q
(219) Absorption: p W q ∧ q ≡ q
(220) Absorption: p W q ∧ (p ∨ q) ≡ p W q
(221) Absorption: p W q ∨ (p ∧ q) ≡ p W q
(222) Left absorption of W : p W (p W q) ≡ p W q
(223) Right absorption of W : (p W q) W q ≡ p W q
(224) □ to W law: □ p ≡ p W false
(225) ◇ to W law: ◇ p ≡ ¬(¬p W false)
(226) W implication: p W q ⇒ □ p ∨ ◇ q
(227) Absorption: p W (p U q) ≡ p W q
(228) Absorption: (p U q) W q ≡ p U q
(229) Absorption: p U (p W q) ≡ p W q
(230) Absorption: (p W q) U q ≡ p U q
(231) Absorption of W into ◇ : ◇ q W q ≡ ◇ q
(232) Absorption of W into □ : □ p ∧ p W q ≡ □ p
(233) Absorption of □ into W : □ p ∨ p W q ≡ p W q
(234) p W q ∧ □ ¬q ⇒ □ p
(235) □ p ⇒ p U q ∨ □ ¬q
(236) ¬□ p ∧ p W q ⇒ ◇ q
(237) ◇ q ⇒ ¬□ p ∨ p U q
(238) Left monotonicity of W : □ (p → q) ⇒ (p W r → q W r)
(239) Right monotonicity of W : □ (p → q) ⇒ (r W p → r W q)
(240) W strengthening rule : □ ((p → r) ∧ (q → s)) ⇒ (p W q → r W s)
(241) W catenation rule: □ ((p → q W r) ∧ (r → q W s)) ⇒ (p → q W s)
(242) Left U W implication: (p U q) W r ⇒ (p W q) W r
(243) Right W U implication: p W (q U r) ⇒ p W (q W r)
(244) Right U U implication: p U (q U r) ⇒ p U (q W r)
(245) Left U U implication: (p U q) U r ⇒ (p W q) U r
(246) Left U ∨ strengthening: (p U q) U r ⇒ (p ∨ q) U r
(247) Left W ∨ strengthening: (p W q) W r ⇒ (p ∨ q) W r
(248) Right W ∨ strengthening: p W (q W r) ⇒ p W (q ∨ r)
(249) Right W ∨ ordering: p W (q W r) ⇒ (p ∨ q) W r
(250) Right ∧ W ordering: p W (q ∧ r) ⇒ (p W q) W r
(251) U ordering: ¬p U q ∨ ¬q U p ≡ ◇ (p ∨ q)
(252) W ordering: ¬p W q ∨ ¬q W p
(253) W implication ordering: p W q ∧ ¬q W r ⇒ p W r
(254) Lemmon formula: □ (□ p → q) ∨ □ (□ q → p)
*)

Axiom (* 169 *) wait_def : forall (φ ψ : t), φ W ψ ≈ □ φ ∨ φ U ψ.

Lemma (* 170 *) not_wait (φ ψ : t) : ¬(φ W ψ) ≈ ¬ψ U (¬φ ∧ ¬ψ).
Proof.
  rewrite wait_def.
  rewrite <- not_until.
  rewrite not_or.
  rewrite always_def.
  rewrite evn_def.
  now boolean.
Qed.

Lemma (* 171 *) law_171 (* U in terms of W *) (φ ψ : t) : φ U ψ ≈ φ W ψ ∧ ◇ ψ.
Proof.
  rewrite wait_def.
  rewrite and_comm.
  rewrite and_or.
  rewrite and_comm.
  split.
  - rewrite or_comm.
    rewrite <- or_inj.
    rewrite and_comm.
    now rewrite law_39.
  - rewrite law_84.
    apply or_impl_iff.
    boolean.
    rewrite not_and.
    rewrite or_assoc.
    now boolean.
Qed.

Lemma (* 172 *) law_172 (**) (φ ψ : t) : φ W ψ ≈ □ (φ ∧ ¬ψ) ∨ φ U ψ.
Proof.
  rewrite law_99.
  rewrite or_comm.
  rewrite or_and.
  rewrite or_comm.
  rewrite <- wait_def.
  rewrite law_171.
  rewrite or_comm.
  rewrite or_and.
  rewrite !(or_comm (always _)).
  rewrite law_89.
  rewrite and_true.
  now rewrite and_absorb.
Qed.

Lemma (* 173 *) law_173 (*Distributivity of ¬ over U *) (φ ψ : t) : ¬(φ U ψ) ≈ ¬ψ W (¬φ ∧ ¬ψ).
Proof.
  rewrite law_171.
  rewrite not_and.
  rewrite not_wait.
  rewrite wait_def.
  rewrite or_comm.
  apply or_respects_eqv; [|reflexivity].
  now apply law_61.
Qed.

Lemma (* 174 *) law_174 (*U implication*) (φ ψ : t) : φ U ψ ⟹ φ W ψ.
Proof.
  rewrite law_171.
  now boolean.
Qed.

Lemma (* 175 *) law_175 (*Distributivity of ∧ over W *) (φ ψ χ : t) : □ φ ∧ ψ W χ ⟹ (φ ∧ ψ) W (φ ∧ χ).
Proof.
  rewrite wait_def.
  rewrite and_or.
  rewrite law_83.
  rewrite <- law_99.
  now rewrite <- wait_def.
Qed.

Lemma (* 176 *) law_176 (*W ◇ equivalence*) (φ ψ : t) : φ W ◇ ψ ≈ □ φ ∨ ◇ ψ.
Proof.
  rewrite wait_def.
  now rewrite until_absorb_evn.
Qed.

Lemma (* 177 *) law_177 (*W □ implication*) (φ ψ : t) : φ W □ ψ ⟹ □ (φ W ψ).
Proof.
  rewrite (wait_def _ ψ).
  rewrite <- law_100.
  rewrite law_72.
  rewrite <- law_140.
  now rewrite <- wait_def.
Qed.

Lemma (* 178 *) law_178 (*Absorption of W into □ *) (φ : t) : φ W □ φ ≈ □ φ.
Proof.
  rewrite wait_def.
  rewrite law_141.
  now boolean.
Qed.

Lemma (* 179 *) law_179 (*Perpetuity*) (φ ψ : t) : □ φ ⟹ φ W ψ.
Proof.
  rewrite (or_inj _ (φ U ψ)).
  now rewrite <- wait_def.
Qed.

Lemma (* 180 *) law_180 (*Distributivity of ◯ over W *) (φ ψ : t) : ◯ (φ W ψ) ≈ ◯ φ W ◯ ψ.
Proof.
  rewrite wait_def.
  rewrite next_or.
  rewrite law_73.
  rewrite next_until.
  now rewrite <- wait_def.
Qed.

Lemma (* 181 *) law_181 (*Expansion of W *) (φ ψ : t) : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).
Proof.
  rewrite wait_def at 2.
  rewrite next_or.
  rewrite and_or.
  rewrite <- law_66.
  rewrite <- or_assoc.
  rewrite (or_comm ψ).
  rewrite or_assoc.
  rewrite <- until_expansion.
  now rewrite <- wait_def.
Qed.

Lemma (* 182 *) law_182 (*W excluded middle*) (φ ψ : t) : φ W ψ ∨ φ W ¬ψ ≈ ⊤.
Proof.
  rewrite law_181.
  rewrite (law_181 _ (¬ψ)).
  rewrite (or_comm ψ).
  rewrite or_assoc.
  rewrite !or_and.
  rewrite <- (or_assoc ψ).
  boolean.
  rewrite <- (or_assoc ψ).
  now boolean.
Qed.

Lemma (* 183 *) law_183 (*Left zero of W *) (ψ : t) : ⊤ W ψ ≈ ⊤.
Proof.
  rewrite wait_def.
  rewrite law_64.
  now boolean.
Qed.

Lemma (* 184 *) law_184 (*Left distributivity of W over ∨ *) (φ ψ χ : t) : φ W (ψ ∨ χ) ≈ φ W ψ ∨ φ W χ.
Proof.
  rewrite wait_def.
  rewrite until_left_or.
  rewrite <- (or_idem (□ φ)).
  rewrite or_assoc.
  rewrite <- (or_assoc (□ φ) (until _ _)).
  rewrite or_comm.
  rewrite !or_assoc.
  rewrite (or_comm (until _ _) (□ φ)).
  rewrite <- wait_def.
  rewrite <- or_assoc.
  now rewrite <- wait_def.
Qed.

Lemma (* 185 *) law_185 (*Right distributivity of W over ∨ *) (φ ψ χ : t) : φ W χ ∨ ψ W χ ⟹ (φ ∨ ψ) W χ.
Proof.
  rewrite 2 wait_def.
  rewrite <- or_assoc.
  rewrite (or_comm _ (□ ψ)).
  rewrite <- or_assoc.
  rewrite (or_comm (□ ψ)).
  rewrite law_100.
  rewrite !or_assoc.
  rewrite until_right_or.
  now rewrite <- wait_def.
Qed.

Lemma (* 186 *) law_186 (*Left distributivity of W over ∧ *) (φ ψ χ : t) : φ W (ψ ∧ χ) ⟹ φ W ψ ∧ φ W χ.
Proof.
  rewrite wait_def.
  rewrite until_left_and.
  rewrite or_and.
  now rewrite <- !wait_def.
Qed.

Lemma (* 187 *) law_187 (*Right distributivity of W over ∧ *) (φ ψ χ : t) : (φ ∧ ψ) W χ ≈ φ W χ ∧ ψ W χ.
Proof.
  rewrite <- not_not.
  rewrite not_wait.
  rewrite (and_comm _ (¬χ)).
  rewrite not_and.
  rewrite and_or.
  rewrite !(and_comm (¬χ)).
  rewrite until_left_or.
  rewrite <- !not_wait.
  rewrite <- not_and.
  now boolean.
Qed.

Lemma (* 188 *) law_188 (*Right distributivity of W over ⟹ *) (φ ψ χ : t) : (φ → ψ) W χ ⟹ (φ W χ → ψ W χ).
Proof.
  apply and_impl_iff.
  rewrite <- law_187.
  rewrite impl_apply.
  rewrite law_187.
  now boolean.
Qed.

Lemma (* 189 *) law_189 (*Disjunction rule of W *) (φ ψ : t) : φ W ψ ≈ (φ ∨ ψ) W ψ.
Proof.
  rewrite <- not_not.
  rewrite not_wait.
  rewrite law_173.
  rewrite !not_and.
  boolean.
  rewrite or_comm.
  now rewrite and_absorb.
Qed.

Lemma (* 190 *) law_190 (*Disjunction rule of U *) (φ ψ : t) : φ U ψ ≈ (φ ∨ ψ) U ψ.
Proof.
  rewrite <- not_not.
  rewrite law_173.
  rewrite not_wait.
  rewrite !not_and.
  boolean.
  rewrite or_comm.
  now rewrite and_absorb.
Qed.

Lemma (* 191 *) law_191 (*Rule of W *) (ψ : t) : ¬ψ W ψ ≈ ⊤.
Proof.
  rewrite law_189.
  boolean.
  now rewrite law_183.
Qed.

Lemma (* 192 *) law_192 (*Rule of U *) (ψ : t) : ¬ψ U ψ ≈ ◇ ψ.
Proof.
  rewrite law_190.
  boolean.
  now rewrite evn_def.
Qed.

Lemma (* 193 *) law_193 (**) (φ ψ : t) : (φ → ψ) W φ ≈ ⊤.
Proof.
  apply true_impl.
  rewrite <- law_185.
  rewrite law_191.
  now boolean.
Qed.

Lemma (* 194 *) law_194 (**) (φ ψ : t) : ◇ φ ⟹ (φ → ψ) U φ.
Proof.
  rewrite <- until_right_or.
  rewrite <- or_inj.
  now rewrite <- law_192.
Qed.

Lemma (* 195 *) law_195 (*Conjunction rule of W *) (φ ψ : t) : φ W ψ ≈ (φ ∧ ¬ψ) W ψ.
Proof.
  rewrite law_187.
  rewrite law_191.
  now boolean.
Qed.

Lemma (* 196 *) law_196 (*Conjunction rule of U *) (φ ψ : t) : φ U ψ ≈ (φ ∧ ¬ψ) U ψ.
Proof.
  rewrite (law_171 (and _ _)).
  rewrite <- law_195.
  now rewrite <- law_171.
Qed.

Lemma (* 197 *) law_197 (*Distributivity of ¬ over W *) (φ ψ : t) : ¬(φ W ψ) ≈ (φ ∧ ¬ψ) U (¬φ ∧ ¬ψ).
Proof.
  rewrite not_wait.
  rewrite law_196.
  rewrite not_and.
  boolean.
  rewrite and_or.
  boolean.
  now rewrite and_comm.
Qed.

Lemma (* 198 *) law_198 (*Distributivity of ¬ over U *) (φ ψ : t) : ¬(φ U ψ) ≈ (φ ∧ ¬ψ) W (¬φ ∧ ¬ψ).
Proof.
  rewrite law_173.
  rewrite law_195.
  rewrite not_and.
  boolean.
  rewrite and_or.
  boolean.
  now rewrite and_comm.
Qed.

Lemma (* 199 *) law_199 (*Dual of U *) (φ ψ : t) : ¬(¬φ U ¬ψ) ≈ ψ W (φ ∧ ψ).
Proof.
  rewrite law_173.
  now boolean.
Qed.

Lemma (* 200 *) law_200 (*Dual of U *) (φ ψ : t) : ¬(¬φ U ¬ψ) ≈ (¬φ ∧ ψ) W (φ ∧ ψ).
Proof.
  rewrite law_198.
  now boolean.
Qed.

Lemma (* 201 *) law_201 (*Dual of W *) (φ ψ : t) : ¬(¬φ W ¬ψ) ≈ ψ U (φ ∧ ψ).
Proof.
  rewrite not_wait.
  now boolean.
Qed.

Lemma (* 202 *) law_202 (*Dual of W *) (φ ψ : t) : ¬(¬φ W ¬ψ) ≈ (¬φ ∧ ψ) U (φ ∧ ψ).
Proof.
  rewrite law_197.
  now boolean.
Qed.

Lemma (* 203 *) law_203 (*Idempotency of W *) (φ : t) : φ W φ ≈ φ.
Proof.
  rewrite wait_def.
  rewrite until_idem.
  now rewrite law_69.
Qed.

Lemma (* 204 *) law_204 (*Right zero of W *) (φ : t) : φ W ⊤ ≈ ⊤.
Proof.
  rewrite wait_def.
  rewrite until_true.
  now boolean.
Qed.

Lemma (* 205 *) law_205 (*Left identity of W *) (ψ : t) : ⊥ W ψ ≈ ψ.
Proof.
  rewrite wait_def.
  rewrite false_until.
  rewrite law_65.
  now boolean.
Qed.

Lemma (* 206 *) law_206 (**) (φ ψ : t) : φ W ψ ⟹ φ ∨ ψ.
Proof.
  rewrite law_181.
  rewrite or_and.
  rewrite or_comm.
  now boolean.
Qed.

Lemma (* 207 *) law_207 (**) (φ ψ : t) : □ (φ ∨ ψ) ⟹ φ W ψ.
Proof.
  rewrite law_179.
  now rewrite <- law_189.
Qed.

Lemma (* 208 *) law_208 (**) (φ ψ : t) : □ (¬ψ → φ) ⟹ φ W ψ.
Proof.
  rewrite or_comm.
  rewrite not_not.
  now rewrite law_207.
Qed.

Lemma (* 209 *) law_209 (*W insertion*) (φ ψ : t) : ψ ⟹ φ W ψ.
Proof.
  rewrite law_181.
  now boolean.
Qed.

Lemma (* 210 *) law_210 (*W frame law of ◯ *) (φ ψ : t) : □ φ ⟹ (◯ ψ → ◯ (φ W ψ)).
Proof.
  rewrite <- next_impl.
  rewrite <- law_209.
  boolean.
  rewrite next_true.
  now apply impl_true.
Qed.

Lemma (* 211 *) law_211 (*W frame law of ◇ *) (φ ψ : t) : □ φ ⟹ (◇ ψ → ◇ (φ W ψ)).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 212 *) law_212 (*W frame law of □ *) (φ ψ : t) : □ φ ⟹ (□ ψ → □ (φ W ψ)).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 213 *) law_213 (*W induction*) (φ ψ χ : t) : □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ (φ → ψ W χ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 214 *) law_214 (*W induction*) (φ ψ : t) : □ (φ → ◯ (φ ∨ ψ)) ⟹ (φ → φ W ψ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 215 *) law_215 (*W induction*) (φ ψ : t) : □ (φ → ◯ φ) ⟹ (φ → φ W ψ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 216 *) law_216 (*W induction*) (φ ψ : t) : □ (φ → ψ ∧ ◯ φ) ⟹ (φ → φ W ψ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 217 *) law_217 (*Absorption*) (φ ψ : t) : φ ∨ φ W ψ ≈ φ ∨ ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 218 *) law_218 (*Absorption*) (φ ψ : t) : φ W ψ ∨ ψ ≈ φ W ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 219 *) law_219 (*Absorption*) (φ ψ : t) : φ W ψ ∧ ψ ≈ ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 220 *) law_220 (*Absorption*) (φ ψ : t) : φ W ψ ∧ (φ ∨ ψ) ≈ φ W ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 221 *) law_221 (*Absorption*) (φ ψ : t) : φ W ψ ∨ (φ ∧ ψ) ≈ φ W ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 222 *) law_222 (*Left absorption of W *) (φ ψ : t) : φ W (φ W ψ) ≈ φ W ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 223 *) law_223 (*Right absorption of W *) (φ ψ : t) : (φ W ψ) W ψ ≈ φ W ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 224 *) law_224 (*□ to W law*) (φ : t) : □ φ ≈ φ W ⊥.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 225 *) law_225 (*◇ to W law*) (φ : t) : ◇ φ ≈ ¬(¬φ W ⊥).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 226 *) law_226 (*W implication*) (φ ψ : t) : φ W ψ ⟹ □ φ ∨ ◇ ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 227 *) law_227 (*Absorption*) (φ ψ : t) : φ W (φ U ψ) ≈ φ W ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 228 *) law_228 (*Absorption*) (φ ψ : t) : (φ U ψ) W ψ ≈ φ U ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 229 *) law_229 (*Absorption*) (φ ψ : t) : φ U (φ W ψ) ≈ φ W ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 230 *) law_230 (*Absorption*) (φ ψ : t) : (φ W ψ) U ψ ≈ φ U ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 231 *) law_231 (*Absorption of W into ◇ *) (ψ : t) : ◇ ψ W ψ ≈ ◇ ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 232 *) law_232 (*Absorption of W into □ *) (φ ψ : t) : □ φ ∧ φ W ψ ≈ □ φ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 233 *) law_233 (*Absorption of □ into W *) (φ ψ : t) : □ φ ∨ φ W ψ ≈ φ W ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 234 *) law_234 (**) (φ ψ : t) : φ W ψ ∧ □ ¬ψ ⟹ □ φ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 235 *) law_235 (**) (φ ψ : t) : □ φ ⟹ φ U ψ ∨ □ ¬ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 236 *) law_236 (**) (φ ψ : t) : ¬□ φ ∧ φ W ψ ⟹ ◇ ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 237 *) law_237 (**) (φ ψ : t) : ◇ ψ ⟹ ¬□ φ ∨ φ U ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* NEW *) law_237b (φ ψ : t) : ◇ ψ ⟹ □ φ → φ U ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 238 *) law_238 (*Left monotonicity of W *) (φ ψ χ : t) : □ (φ → ψ) ⟹ (φ W χ → ψ W χ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 239 *) law_239 (*Right monotonicity of W *) (φ ψ χ : t) : □ (φ → ψ) ⟹ (χ W φ → χ W ψ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 240 *) law_240 (*W strengthening rule *) (φ ψ χ ρ : t) : □ ((φ → χ) ∧ (ψ → ρ)) ⟹ (φ W ψ → χ W ρ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 241 *) law_241 (*W catenation rule*) (φ ψ χ ρ : t) : □ ((φ → ψ W χ) ∧ (χ → ψ W ρ)) ⟹ (φ → ψ W ρ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 242 *) law_242 (*Left U W implication*) (φ ψ χ : t) : (φ U ψ) W χ ⟹ (φ W ψ) W χ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 243 *) law_243 (*Right W U implication*) (φ ψ χ : t) : φ W (ψ U χ) ⟹ φ W (ψ W χ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 244 *) law_244 (*Right U U implication*) (φ ψ χ : t) : φ U (ψ U χ) ⟹ φ U (ψ W χ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 245 *) law_245 (*Left U U implication*) (φ ψ χ : t) : (φ U ψ) U χ ⟹ (φ W ψ) U χ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 246 *) law_246 (*Left U ∨ strengthening*) (φ ψ χ : t) : (φ U ψ) U χ ⟹ (φ ∨ ψ) U χ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 247 *) law_247 (*Left W ∨ strengthening*) (φ ψ χ : t) : (φ W ψ) W χ ⟹ (φ ∨ ψ) W χ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 248 *) law_248 (*Right W ∨ strengthening*) (φ ψ χ : t) : φ W (ψ W χ) ⟹ φ W (ψ ∨ χ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 249 *) law_249 (*Right W ∨ ordering*) (φ ψ χ : t) : φ W (ψ W χ) ⟹ (φ ∨ ψ) W χ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 250 *) law_250 (*Right ∧ W ordering*) (φ ψ χ : t) : φ W (ψ ∧ χ) ⟹ (φ W ψ) W χ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 251 *) law_251 (*U ordering*) (φ ψ : t) : ¬φ U ψ ∨ ¬ψ U φ ≈ ◇ (φ ∨ ψ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 252 *) law_252 (*W ordering*) (φ ψ : t) : ¬φ W ψ ∨ ¬ψ W φ ≈ ⊤.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 253 *) law_253 (*W implication ordering*) (φ ψ χ : t) : φ W ψ ∧ ¬ψ W χ ⟹ φ W χ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma (* 254 *) law_254 (*Lemmon formula*) (φ ψ : t) : □ (□ φ → ψ) ∨ □ (□ ψ → φ) ≈ ⊤.
Proof.
  (* FILL IN HERE *)
Admitted.

(*** Release R *)

Axiom release_def : forall (φ ψ : t), φ R ψ ≈ ¬(¬φ U ¬ψ).

Lemma law_256 (φ ψ : t) : φ U ψ ≈ ¬(¬φ R ¬ψ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_257 (φ ψ : t) : φ W ψ ≈ ψ R (ψ ∨ φ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_258 (φ ψ : t) : φ R ψ ≈ ψ W (ψ ∧ φ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_259 (φ ψ : t) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_260 (φ ψ χ : t) : φ R (ψ ∨ χ) ≈ (φ R ψ) ∨ (φ R χ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_261 (φ ψ χ : t) : (φ ∧ ψ) R χ ≈ (φ R χ) ∧ (ψ R χ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_262 (φ ψ : t) : ◯ (φ R ψ) ≈ ◯ φ R ◯ ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_263 (φ ψ : t) : □ ψ ≈ ⊥ R ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_264 (φ ψ : t) : ¬(φ U ψ) ≈ ¬φ R ¬ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_265 (φ ψ : t) : ¬(φ R ψ) ≈ ¬φ U ¬ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

(*** Strong Release M *)

Axiom strong_release_def : forall (φ ψ : t), φ M ψ ≈ φ U (ψ ∧ φ).

Lemma law_266 (φ ψ : t) : φ W ψ ≈ ¬(¬φ M ¬ψ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_267 (φ ψ : t) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_268 (φ ψ : t) : φ M ψ ≈ φ R ψ ∧ ◇ φ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_269 (φ ψ : t) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Proof.
  (* FILL IN HERE *)
Admitted.

(*** OLD *)

Notation "p ≉ q" := (~ (p ≈ q)) (at level 90, no associativity).

Lemma law_270 (φ ψ χ : t) : □ (φ → ¬ψ ∧ ◯ χ) ⟹ φ → ¬(ψ U χ).
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_271 (φ ψ χ ρ : t) : □ ((φ → ψ U χ) ∧ (χ → ψ U ρ)) ⟹ φ → □ χ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_272 (φ ψ : t) : ◇ (φ U ψ) ≉ ◇ φ U ◇ ψ.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma law_273 (φ ψ : t) : ¬◇ (¬φ ∧ ψ) ≈ □ (φ ∨ ¬ψ).
Proof.
  (* FILL IN HERE *)
Admitted.

(* Definition examine {a : Type} (P : a -> t) : t := fun s => P (head s) s. *)

End LinearTemporalLogic.
