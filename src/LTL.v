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
Declare Instance strong_release_respects_impl :
  Proper (impl ==> impl ==> impl) strong_release.
Program Instance strong_release_respects_eqv :
  Proper (eqv ==> eqv ==> eqv) strong_release.

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

Hypothesis (* 38 *) evn_def : forall (φ : t), ◇ φ ≈ ⊤ U φ.

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
(54) Deﬁnition of □ : □ p ≡ ¬◇ ¬p
(55) Axiom, U Induction: □ (p ⇒ (◯ p ∧ q) ∨ r) ⇒ (p ⇒ □ q ∨ q U r)
(56) Axiom, U Induction: □ (p ⇒ ◯ (p ∨ q)) ⇒ (p ⇒ □ p ∨ p U q)
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

Hypothesis (* 54 *) always_def : forall (φ : t), □ φ ≈ ¬◇ ¬φ.
Hypothesis (* 55 *) always_until_and_ind : forall (φ ψ χ : t),
  □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ φ → □ ψ ∨ ψ U χ.
Hypothesis (* 56 *) always_until_or_ind : forall (φ ψ : t),
  □ (φ → ◯ (φ ∨ ψ)) ⟹ φ → □ φ ∨ φ U ψ.

Lemma (* 57 *) always_induction (φ : t) : □ (φ → ◯ φ) ⟹ (φ → □ φ).
Proof.
  pose proof (always_until_or_ind φ ⊥).
  rewrite until_right_bottom in H.
  now rewrite !or_false in H.
Qed.

Lemma (* 58 *) evn_induction (φ : t) : □ (◯ φ → φ) ⟹ (◇ φ → φ).
Proof.
  pose proof (always_until_or_ind (¬ φ) ⊥).
  rewrite until_right_bottom in H.
  rewrite !or_false in H.
  rewrite next_linearity in H.
  rewrite !not_not in H.
  rewrite or_comm in H.
  rewrite H; clear H.
  rewrite always_def.
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

(*** Release R *)

Hypothesis release_def : forall (φ ψ : t), φ R ψ ≈ ¬(¬φ U ¬ψ).

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

Hypothesis strong_release_def : forall (φ ψ : t), φ M ψ ≈ φ U (ψ ∧ φ).

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

(* Definition examine {a : Type} (P : a -> t) : t := fun s => P (head s) s. *)

End LinearTemporalLogic.
