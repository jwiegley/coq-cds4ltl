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

Notation "◇ p"     := (eventually p) (at level 0, right associativity).
Notation "□ p"     := (always p)     (at level 0, right associativity).
Notation "p 'W' q" := (wait p q)     (at level 44, right associativity).

(*** 3.3 Eventually ◇ *)

(**
(38) Deﬁnition of ◇ : ◇ q ≡ true U q
(39) Absorption of ◇ into U : p U q ∧ ◇ q ≡ p U q
(40) Absorption of U into ◇ : p U q ∨ ◇ q ≡ ◇ q
(41) Absorption of U into ◇ : p U ◇ q ≡ ◇ q
(42) Eventuality: p U q ⟹ ◇ q
(43) Truth of ◇ : ◇ true ≡ true
(44) Falsehood of ◇ : ◇ false ≡ false
(45) Expansion of ◇ : ◇ p ≡ p ∨ ◯ ◇ p
(46) Weakening of ◇ : p ⟹ ◇ p
(47) Weakening of ◇ : ◯ p ⟹ ◇ p
(48) Absorption of ∨ into ◇ : p ∨ ◇ p ≡ ◇ p
(49) Absorption of ◇ into ∧ : ◇ p ∧ p ≡ p
(50) Absorption of ◇ : ◇ ◇ p ≡ ◇ p
(51) Exchange of ◯ and ◇ : ◯ ◇ p ≡ ◇ ◯ p
(52) Distributivity of ◇ over ∨ : ◇ (p ∨ q) ≡ ◇ p ∨ ◇ q
(53) Distributivity of ◇ over ∧ : ◇ (p ∧ q) ⟹ ◇ p ∧ ◇ q
*)

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

(*** 3.4 Always □ *)

(**
(54) Deﬁnition of □ : □ p ≡ ¬◇ ¬p
(55) Axiom, U Induction: □ (p ⇒ (◯ p ∧ q) ∨ r) ⇒ (p ⇒ □ q ∨ q U r)
(56) Axiom, U Induction: □ (p ⇒ ◯ (p ∨ q)) ⇒ (p ⇒ □ p ∨ p U q)
(57) □ Induction: □ (p → ◯ p) ⟹ (p → □ p)
(58) ◇ Induction: □ ( ◯ p → p) ⟹ (◇ p → p)
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
(75) p ∧ ◇ ¬p ⟹ ◇ (p ∧ ◯ ¬p)
(76) Strengthening of □ : □ p ⟹ p
(77) Strengthening of □ : □ p ⟹ ◇ p
(78) Strengthening of □ : □ p ⟹ ◯ p
(79) Strengthening of □ : □ p ⟹ ◯ □
(80) ◯ generalization: □ p ⟹ □ ◯ p
(81) □ p ⟹ ¬(q U ¬p)
*)

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

(**
(82) Temporal deduction:
     To prove □ P₁ ∧ □ P₂ ⇒ Q, assume P₁ and P₂, and prove Q.
     You cannot use textual substitution in P₁ or P₂.
*)

Lemma (* 82 *) temporal_deduction (φ ψ : t) : (φ ≈ ⊤ -> ψ ≈ ⊤) -> □ φ ⟹ ψ.
Proof.
Admitted.

(*** 3.6 Always □, Continued *)

(**
(83) Distributivity of ∧ over U : □ p ∧ q U r ⟹ (p ∧ q) U (p ∧ r)
(84) U implication: □ p ∧ ◇ q ⟹ p U q
(85) Right monotonicity of U : □ (p → q) ⟹ (r U p → r U q)
(86) Left monotonicity of U : □ (p → q) ⟹ (p U r → q U r)
(87) Distributivity of ¬ over □ : □ ¬p ⟹ ¬□ p
(88) Distributivity of ◇ over ∧ : □ p ∧ ◇ q ⟹ ◇ (p ∧ q)
(89) ◇ excluded middle: ◇ p ∨ □ ¬p
(90) □ excluded middle: □ p ∨ ◇ ¬p
(91) Temporal excluded middle: ◇ p ∨ ◇ ¬p
(92) ◇ contradiction: ◇ p ∧ □ ¬p ≡ false
(93) □ contradiction: □ p ∧ ◇ ¬p ≡ false
(94) Temporal contradiction: □ p ∧ □ ¬p ≡ false
(95) □ ◇ excluded middle: □ ◇ p ∨ ◇ □ ¬p
(96) ◇ □ excluded middle: ◇ □ p ∨ □ ◇ ¬p
(97) □ ◇ contradiction: □ ◇ p ∧ ◇ □ ¬p ≡ false
(98) ◇ □ contradiction: ◇ □ p ∧ □ ◇ ¬p ≡ false
(99) Distributivity of □ over ∧ : □ (p ∧ q) ≡ □ p ∧ □ q
(100) Distributivity of □ over ∨ : □ p ∨ □ q ⟹ □ (p ∨ q)
(101) Logical equivalence law of ◯ : □ (p ≡ q) ⟹ ( ◯ p ≡ ◯ q)
(102) Logical equivalence law of ◇ : □ (p ≡ q) ⟹ (◇ p ≡ ◇ q)
(103) Logical equivalence law of □ : □ (p ≡ q) ⟹ (□ p ≡ □ q)
(104) Distributivity of ◇ over ⟹ : ◇ (p → q) ≡ (□ p → ◇ q)
(105) Distributivity of ◇ over ⟹ : (◇ p → ◇ q) ⟹ ◇ (p → q)
(106) ∧ frame law of ◯ : □ p ⟹ ( ◯ q → ◯ (p ∧ q))
(107) ∧ frame law of ◇ : □ p ⟹ (◇ q → ◇ (p ∧ q))
(108) ∧ frame law of □ : □ p ⟹ (□ q → □ (p ∧ q))
(109) ∨ frame law of ◯ : □ p ⟹ ( ◯ q → ◯ (p ∨ q))
(110) ∨ frame law of ◇ : □ p ⟹ (◇ q → ◇ (p ∨ q))
(111) ∨ frame law of □ : □ p ⟹ (□ q → □ (p ∨ q))
(112) ⟹ frame law of ◯ : □ p ⟹ ( ◯ q → ◯ (p → q))
(113) ⟹ frame law of ◇ : □ p ⟹ (◇ q → ◇ (p → q))
(114) ⟹ frame law of □ : □ p ⟹ (□ q → □ (p → q))
(115) ≡ frame law of ◯ : □ p ⟹ ( ◯ q → ◯ (p ≡ q))
(116) ≡ frame law of ◇ : □ p ⟹ (◇ q → ◇ (p ≡ q))
(117) ≡ frame law of □ : □ p ⟹ (□ q → □ (p ≡ q))
(118) Monotonicity of ◯ : □ (p → q) ⟹ ( ◯ p → ◯ q)
(119) Monotonicity of ◇ : □ (p → q) ⟹ (◇ p → ◇ q)
(120) Monotonicity of □ : □ (p → q) ⟹ (□ p → □ q)
(121) Consequence rule of ◯ : □ ((p → q) ∧ (q → ◯ r) ∧ (r → s)) ⟹ (p → ◯ s)
(122) Consequence rule of ◇ : □ ((p → q) ∧ (q → ◇ r) ∧ (r → s)) ⟹ (p → ◇ s)
(123) Consequence rule of □ : □ ((p → q) ∧ (q → □ r) ∧ (r → s)) ⟹ (p → □ s)
(124) Catenation rule of ◇ : □ ((p → ◇ q) ∧ (q → ◇ r)) ⟹ (p → ◇ r)
(125) Catenation rule of □ : □ ((p → □ q) ∧ (q → □ r)) ⟹ (p → □ r)
(126) Catenation rule of U : □ ((p → q U r) ∧ (r → q U s)) ⟹ (p → q U s)
(127) U strengthening rule: □ ((p → r) ∧ (q → s)) ⟹ (p U q → r U s)
(128) Induction rule ◇ : □ (p ∨ ◯ q → q) ⟹ (◇ p → q)
(129) Induction rule □ : □ (p → q ∧ ◯ p) ⟹ (p → □ q)
(130) Induction rule U : □ (p → ¬q ∧ ◯ p) ⟹ (p → ¬(r U q))
(131) ◇ Conﬂuence: □ ((p → ◇ (q ∨ r)) ∧ (q → ◇ t) ∧ (r → ◇ t)) ⟹ (p → ◇ t)
(132) Temporal generalization law: □ (□ p → q) ⟹ (□ p → □ q)
(133) Temporal particularization law: □ (p → ◇ q) ⟹ (◇ p → ◇ q)
(134) □ (p → ◯ q) ⟹ (p → ◇ q)
(135) □ (p → ◯ ¬p) ⟹ (p → ¬□ p)
*)

Lemma (* 83 *) law (φ ψ χ : t) : □ φ ∧ (ψ U χ) ⟹ (φ ∧ ψ) U (φ ∧ χ).
Proof.
  apply and_impl_iff.
  apply temporal_deduction; intros.
  rewrite H.
  rewrite !true_and.
  rewrite or_comm.
  now apply true_def.
Qed.

(*** 3.7 Proof Metatheorems *)

(**
(136) Metatheorem: P is a theorem iff □ P is a theorem.
(137) Metatheorem ◯ : If P ⇒ Q is a theorem then ◯ P ⇒ ◯ Q is a theorem.
(138) Metatheorem ◇ : If P ⇒ Q is a theorem then ◇ P ⇒ ◇ Q is a theorem.
(139) Metatheorem □ : If P ⇒ Q is a theorem then □ P ⇒ □ Q is a theorem.
*)

(*
Lemma (* 136 *) metatheorem (ϕ : t) : ϕ is a theorem <-> □ ϕ is a theorem.
*)

Lemma (* 137 *) next_metatheorem (φ ψ : t) : φ ⟹ ψ -> ◯ φ ⟹ ◯ ψ.
Proof. now apply next_respects_impl. Qed.

Lemma (* 138 *) eventually_metatheorem (φ ψ : t) : φ ⟹ ψ -> ◇ φ ⟹ ◇ ψ.
Proof. now apply eventually_respects_impl. Qed.

Lemma (* 139 *) always_metatheorem (φ ψ : t) : φ ⟹ ψ -> □ φ ⟹ □ ψ.
Proof. now apply always_respects_impl. Qed.

(*** 3.8 Always □, Continued *)

(**
(140) U □ implication: p U □ q ⟹ □ (p U q)
(141) Absorption of U into □ : p U □ p ≡ □ p
(142) Right ∧ U strengthening: p U (q ∧ r) ⟹ p U (q U r)
(143) Left ∧ U strengthening: (p ∧ q) U r ⟹ (p U q) U r
(144) Left ∧ U ordering: (p ∧ q) U r ⟹ p U (q U r)
(145) ◇ □ implication: ◇ □ p ⟹ □ ◇ p
(146) □ ◇ excluded middle: □ ◇ p ∨ □ ◇ ¬p
(147) ◇ □ contradiction: ◇ □ p ∧ ◇ □ ¬p ≡ false
(148) U frame law of ◯ : □ p ⟹ ( ◯ q → ◯ (p U q))
(149) U frame law of ◇ : □ p ⟹ (◇ q → ◇ (p U q))
(150) U frame law of □ : □ p ⟹ (□ q → □ (p U q))
(151) Absorption of ◇ into □ ◇ : ◇ □ ◇ p ≡ □ ◇ p
(152) Absorption of □ into ◇ □ : □ ◇ □ p ≡ ◇ □ p
(153) Absorption of □ ◇ : □ ◇ □ ◇ p ≡ □ ◇ p
(154) Absorption of ◇ □ : ◇ □ ◇ □ p ≡ ◇ □ p
(155) Absorption of ◯ into □ ◇ : ◯ □ ◇ p ≡ □ ◇ p
(156) Absorption of ◯ into ◇ □ : ◯ ◇ □ p ≡ ◇ □ p
(157) Monotonicity of □ ◇ : □ (p → q) ⟹ (□ ◇ p → □ ◇ q)
(158) Monotonicity of ◇ □ : □ (p → q) ⟹ (◇ □ p → ◇ □ q)
(159) Distributivity of □ ◇ over ∧ : □ ◇ (p ∧ q) ⟹ □ ◇ p ∧ □ ◇ q
(160) Distributivity of ◇ □ over ∨ : ◇ □ p ∨ ◇ □ q ⟹ ◇ □ (p ∨ q)
(161) Distributivity of □ ◇ over ∨ : □ ◇ (p ∨ q) ≡ □ ◇ p ∨ □ ◇ q
(162) Distributivity of ◇ □ over ∧ : ◇ □ (p ∧ q) ≡ ◇ □ p ∧ ◇ □ q
(163) Eventual latching: ◇ □ (p → □ q) ≡ ◇ □ ¬p ∨ ◇ □ q
(164) □ (□ ◇ p → ◇ q) ≡ ◇ □ ¬p ∨ □ ◇ q
(165) □ ((p ∨ □ q) ∧ (□ p ∨ q)) ≡ □ p ∨ □ q
(166) ◇ □ p ∧ □ ◇ q ⟹ □ ◇ (p ∧ q)
(167) □ ((□ p → ◇ q) ∧ (q → ◯ r)) ⟹ (□ p → ◯ □ ◇ r)
(168) Progress proof rule: □ p ∧ □ (□ p → ◇ q) ⟹ ◇ q
*)

(*** 3.9 Wait W *)

(*
(169) Deﬁnition of W : p W q ≡ □ p ∨ p U q
(170) Axiom, Distributivity of ¬ over W : ¬(p W q) ≡ ¬q U (¬p ∧ ¬q)
(171) U in terms of W : p U q ≡ p W q ∧ ◇ q
(172) p W q ≡ □ (p ∧ ¬q) ∨ p U q
(173) Distributivity of ¬ over U : ¬(p U q) ≡ ¬q W (¬p ∧ ¬q)
(174) U implication: p U q ⟹ p W q
(175) Distributivity of ∧ over W : □ p ∧ q W r ⟹ (p ∧ q) W (p ∧ r)
(176) W ◇ equivalence: p W ◇ q ≡ □ p ∨ ◇ q
(177) W □ implication: p W □ q ⟹ □ (p W q)
(178) Absorption of W into □ : p W □ p ≡ □ p
(179) Perpetuity: □ p ⟹ p W q
(180) Distributivity of ◯ over W : ◯ (p W q) ≡ ◯ p W ◯ q
(181) Expansion of W : p W q ≡ q ∨ (p ∧ ◯ (p W q))
(182) W excluded middle: p W q ∨ p W ¬q
(183) Left zero of W : true W q ≡ true
(184) Left distributivity of W over ∨ : p W (q ∨ r) ≡ p W q ∨ p W r
(185) Right distributivity of W over ∨ : p W r ∨ q W r ⟹ (p ∨ q) W r
(186) Left distributivity of W over ∧ : p W (q ∧ r) ⟹ p W q ∧ p W r
(187) Right distributivity of W over ∧ : (p ∧ q) W r ≡ p W r ∧ q W r
(188) Right distributivity of W over ⟹ : (p → q) W r ⟹ (p W r → q W r)
(189) Disjunction rule of W : p W q ≡ (p ∨ q) W q
(190) Disjunction rule of U : p U q ≡ (p ∨ q) U q
(191) Rule of W : ¬q W q
(192) Rule of U : ¬q U q ≡ ◇ q
(193) (p ⟹ q) W p
(194) ◇ p ⟹ (p → q) U p
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
(206) p W q ⟹ p ∨ q
(207) □ (p ∨ q) ⟹ p W q
(208) □ (¬q → p) ⟹ p W q
(209) W insertion: q ⟹ p W q
(210) W frame law of ◯ : □ p ⟹ ( ◯ q → ◯ (p W q))
(211) W frame law of ◇ : □ p ⟹ (◇ q → ◇ (p W q))
(212) W frame law of □ : □ p ⟹ (□ q → □ (p W q))
(213) W induction: □ (p → ( ◯ p ∧ q) ∨ r) ⟹ (p → q W r)
(214) W induction: □ (p → ◯ (p ∨ q)) ⟹ (p → p W q)
(215) W induction: □ (p → ◯ p) ⟹ (p → p W q)
(216) W induction: □ (p → q ∧ ◯ p) ⟹ (p → p W q)
(217) Absorption: p ∨ p W q ≡ p ∨ q
(218) Absorption: p W q ∨ q ≡ p W q
(219) Absorption: p W q ∧ q ≡ q
(220) Absorption: p W q ∧ (p ∨ q) ≡ p W q
(221) Absorption: p W q ∨ (p ∧ q) ≡ p W q
(222) Left absorption of W : p W (p W q) ≡ p W q
(223) Right absorption of W : (p W q) W q ≡ p W q
(224) □ to W law: □ p ≡ p W false
(225) ◇ to W law: ◇ p ≡ ¬(¬p W false)
(226) W implication: p W q ⟹ □ p ∨ ◇ q
(227) Absorption: p W (p U q) ≡ p W q
(228) Absorption: (p U q) W q ≡ p U q
(229) Absorption: p U (p W q) ≡ p W q
(230) Absorption: (p W q) U q ≡ p U q
(231) Absorption of W into ◇ : ◇ q W q ≡ ◇ q
(232) Absorption of W into □ : □ p ∧ p W q ≡ □ p
(233) Absorption of □ into W : □ p ∨ p W q ≡ p W q
(234) p W q ∧ □ ¬q ⟹ □ p
(235) □ p ⟹ p U q ∨ □ ¬q
(236) ¬□ p ∧ p W q ⟹ ◇ q
(237) ◇ q ⟹ ¬□ p ∨ p U q
(238) Left monotonicity of W : □ (p → q) ⟹ (p W r → q W r)
(239) Right monotonicity of W : □ (p → q) ⟹ (r W p → r W q)
(240) W strengthening rule : □ ((p → r) ∧ (q → s)) ⟹ (p W q → r W s)
(241) W catenation rule: □ ((p → q W r) ∧ (r → q W s)) ⟹ (p → q W s)
(242) Left U W implication: (p U q) W r ⟹ (p W q) W r
(243) Right W U implication: p W (q U r) ⟹ p W (q W r)
(244) Right U U implication: p U (q U r) ⟹ p U (q W r)
(245) Left U U implication: (p U q) U r ⟹ (p W q) U r
(246) Left U ∨ strengthening: (p U q) U r ⟹ (p ∨ q) U r
(247) Left W ∨ strengthening: (p W q) W r ⟹ (p ∨ q) W r
(248) Right W ∨ strengthening: p W (q W r) ⟹ p W (q ∨ r)
(249) Right W ∨ ordering: p W (q W r) ⟹ (p ∨ q) W r
(250) Right ∧ W ordering: p W (q ∧ r) ⟹ (p W q) W r
(251) U ordering: ¬p U q ∨ ¬q U p ≡ ◇ (p ∨ q)
(252) W ordering: ¬p W q ∨ ¬q W p
(253) W implication ordering: p W q ∧ ¬q W r ⟹ p W r
(254) Lemmon formula: □ (□ p → q) ∨ □ (□ q → p)
*)

Hypothesis (* 169 *) wait_def : forall (φ ψ : t), φ W ψ ≈ □ φ ∨ (φ U ψ).
Hypothesis (* 170 *) wait_distr_not : forall (φ ψ : t), ¬(φ W ψ) ≈ ¬ ψ U (¬ φ ∧ ¬ ψ).

Lemma law_182 (φ : t) : φ W φ ≈ φ.
Lemma law_183 (φ ψ : t) : φ W ψ ≈ (φ U ψ) ∨ □ φ.
Lemma law_184 (φ ψ : t) : ¬(φ W ψ) ≈ ¬ ψ U (¬ φ ∧ ¬ ψ).
Lemma law_185 (φ ψ : t) : ¬(φ W ψ) ≈ (φ ∧ ¬ ψ) U (¬ φ ∧ ¬ ψ).
Lemma law_186 (φ ψ : t) : ¬(φ U ψ) ≈ ¬ ψ W (¬ φ ∧ ¬ ψ).
Lemma law_187 (φ ψ : t) : ¬(φ U ψ) ≈ (φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ).
Lemma law_188 (φ ψ : t) : ¬(¬ φ U ¬ ψ) ≈ ψ W (φ ∧ ψ).
Lemma law_189 (φ ψ : t) : ¬(¬ φ U ¬ ψ) ≈ (¬ φ ∧ ψ) W (φ ∧ ψ).
Lemma law_190 (φ ψ : t) : ¬(¬ φ W ¬ ψ) ≈ ψ U (φ ∧ ψ).
Lemma law_191 (φ ψ : t) : ¬(¬ φ W ¬ ψ) ≈ (¬ φ ∧ ψ) U (φ ∧ ψ).
Lemma law_192 (φ ψ : t) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Lemma law_193 (φ ψ : t) : φ W ψ ≈ (φ ∨ ψ) W ψ.
Lemma law_194 (φ ψ : t) : φ W ψ ≈ □ (φ ∧ ¬ ψ) ∨ (φ U ψ).
Lemma law_195 (φ ψ : t) : φ U ψ ≈ (φ W ψ) ∧ ◇ ψ.
Lemma law_196 (φ ψ : t) : φ U ψ ≈ (φ W ψ) ∧ ¬□¬ ψ.
Lemma law_197 (φ ψ : t) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Lemma law_198 (φ ψ : t) : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).
Lemma law_199 (φ ψ : t) : φ W ψ ≈ (φ ∧ ¬ ψ) W ψ.
Lemma law_200 (φ ψ : t) : φ W (φ W ψ) ≈ φ W ψ.
Lemma law_201 (φ ψ : t) : (φ W ψ) W ψ ≈ φ W ψ.
Lemma law_202 (φ ψ : t) : φ W (φ U ψ) ≈ φ W ψ.
Lemma law_203 (φ ψ : t) : (φ U ψ) W ψ ≈ φ U ψ.
Lemma law_204 (φ ψ : t) : φ U (φ W ψ) ≈ φ W ψ.
Lemma law_205 (φ ψ : t) : (φ W ψ) U ψ ≈ φ U ψ.
Lemma law_206 (φ ψ : t) : ◯ (φ W ψ) ≈ ◯ φ W ◯ ψ.
Lemma law_207 (φ ψ : t) : φ W ◇ ψ ≈ □ φ ∨ ◇ ψ.
Lemma law_208 (φ : t) : ◇ φ W φ ≈ ◇ φ.
Lemma law_209 (φ ψ : t) : □ φ ∧ (φ W ψ) ≈ □ φ.
Lemma law_210 (φ ψ : t) : □ φ ∨ (φ W ψ) ≈ φ W ψ.
Lemma law_211 (φ : t) : φ W □ φ ≈ □ φ.
Lemma law_212 (φ : t) : □ φ ≈ φ W ⊥.
Lemma law_213 (φ : t) : ◇ φ ≈ ¬(¬ φ W ⊥).
Lemma law_214 (φ : t) : ⊤ W φ ≈ ⊤.
Lemma law_215 (φ : t) : φ W (⊤) ≈ ⊤.
Lemma law_216 (φ : t) : ⊥ W φ ≈ φ.
Lemma law_217 (φ ψ χ : t) : φ W (ψ ∨ χ) ≈ (φ W ψ) ∨ (φ W χ).
Lemma law_218 (φ ψ χ : t) : (φ ∧ ψ) W χ ≈ (φ W χ) ∧ (ψ W χ).
Lemma law_219 (φ ψ : t) : φ ∨ (φ W ψ) ≈ φ ∨ ψ.
Lemma law_220 (φ ψ : t) : (φ W ψ) ∨ ψ ≈ φ W ψ.
Lemma law_221 (φ ψ : t) : (φ W ψ) ∧ ψ ≈ ψ.
Lemma law_222 (φ ψ : t) : (φ W ψ) ∧ (φ ∨ ψ) ≈ φ W ψ.
Lemma law_223 (φ ψ : t) : (φ W ψ) ∨ (φ ∧ ψ) ≈ φ W ψ.
Lemma law_224 (φ ψ : t) : ((¬ φ U ψ) ∨ (¬ ψ U φ)) ≈ ◇ (φ ∨ ψ).
Lemma law_225 (φ ψ : t) : ψ ⟹ φ W ψ.
Lemma law_226 (φ ψ : t) : φ W φ ⟹ φ ∨ ψ.
Lemma law_227 (φ ψ : t) : φ W φ ⟹ □ φ ∨ ◇ ψ.
Lemma law_228 (φ : t) : ¬ φ W φ ≈ ⊤.
Lemma law_229 (φ ψ : t) : (φ → ψ) W φ ≈ ⊤.
Lemma law_230 (φ ψ : t) : (φ W ψ) ∨ (φ W ¬ ψ) ≈ ⊤.
Lemma law_231 (φ ψ χ : t) : (φ W (ψ ∧ χ)) ⟹ ((φ W ψ) ∧ (φ W χ)).
Lemma law_232 (φ ψ χ : t) : (φ W χ) ∨ (ψ W χ) ⟹ ((φ ∨ ψ) W χ).
Lemma law_233 (φ ψ : t) : φ U ψ ⟹ φ W ψ.
Lemma law_234 (φ ψ : t) : φ W □ ψ ⟹ □ (φ W ψ).
Lemma law_235 (φ ψ : t) : ¬ (φ U ψ) ⟹ ((φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ)).
Lemma law_236 (φ ψ : t) : ¬ (φ W ψ) ⟹ ((φ ∧ ¬ ψ) U (¬ φ ∧ ¬ ψ)).
Lemma law_237 (φ ψ χ : t) : (φ → ψ) W χ ⟹ ((φ W χ) → (ψ W χ)).
Lemma law_238 (φ ψ : t) : □ φ ⟹ φ W ψ.
Lemma law_239 (φ ψ : t) : □ φ ⟹ (◯ ψ → ◯ (φ W ψ)).
Lemma law_240 (φ ψ : t) : □ φ ⟹ (◇ ψ → ◇ (φ W ψ)).
Lemma law_241 (φ ψ : t) : □ φ ⟹ (□ ψ → □ (φ W ψ)).
Lemma law_242 (φ ψ : t) : □ (φ ∨ ψ) ⟹ φ W ψ.
Lemma law_243 (φ ψ : t) : □ (¬ ψ → φ) ⟹ φ W ψ.
Lemma law_244 (φ ψ χ : t) : □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ φ → ψ W χ.
Lemma law_245 (φ ψ : t) : □ (φ → ◯ (φ ∨ ψ)) ⟹ φ → φ W ψ.
Lemma law_246 (φ ψ : t) : □ (φ → ◯ φ) ⟹ φ → φ W ψ.
Lemma law_247 (φ ψ : t) : □ (φ → ψ ∧ ◯ φ) ⟹ φ → φ W ψ.
Lemma law_248 (φ ψ χ : t) : □ φ ∧ (ψ W χ) ⟹ ((φ ∧ ψ) W (φ ∧ χ)).
Lemma law_249 (φ ψ : t) : (φ W ψ) ∧ □¬ ψ ⟹ □ φ.
Lemma law_250 (φ ψ : t) : □ φ ⟹ ((φ U ψ) ∨ □¬ ψ).
Lemma law_251 (φ ψ : t) : ¬□ φ ∧ (φ W ψ) ⟹ ◇ ψ.
Lemma law_252 (φ ψ : t) : ◇ ψ ⟹ (¬□ φ ∨ (φ U ψ)).
Lemma law_253 (φ ψ χ : t) : □ (φ → ψ) ⟹ φ W χ → ψ W χ.
Lemma law_254 (φ ψ χ : t) : □ (φ → ψ) ⟹ χ W φ → χ W ψ.
Lemma law_255 (φ ψ χ ρ : t) : □ ((φ → χ) ∧ (ψ → ρ)) ⟹ ((φ W ψ) → (χ W ρ)).
Lemma law_256 (φ ψ χ ρ : t) : □ ((φ → ψ W χ) ∧ (χ → ψ W ρ)) ⟹ φ → ψ W ρ.
Lemma law_257 (φ ψ χ : t) : (φ U ψ) W χ ⟹ ((φ W ψ) W χ).
Lemma law_258 (φ ψ χ : t) : φ W (ψ U χ) ⟹ (φ W (ψ W χ)).
Lemma law_259 (φ ψ χ : t) : φ U (ψ U χ) ⟹ (φ U (ψ W χ)).
Lemma law_260 (φ ψ χ : t) : (φ U ψ) U χ ⟹ ((φ W ψ) U χ).
Lemma law_261 (φ ψ χ : t) : (φ U ψ) U χ ⟹ ((φ ∨ ψ) U χ).
Lemma law_262 (φ ψ χ : t) : (φ W ψ) W χ ⟹ ((φ ∨ ψ) W χ).
Lemma law_263 (φ ψ χ : t) : φ W (ψ W χ) ⟹ (φ W (ψ ∨ χ)).
Lemma law_264 (φ ψ χ : t) : φ W (ψ W χ) ⟹ ((φ ∨ ψ) W χ).
Lemma law_265 (φ ψ χ : t) : φ W (ψ ∧ χ) ⟹ ((φ W ψ) W χ).
Lemma law_266 (φ ψ : t) : (¬ φ W ψ) ∨ (¬ ψ W φ) ≈ ⊤.
Lemma law_267 (φ ψ χ : t) : (φ W ψ) ∧ (¬ ψ W χ) ⟹ φ W χ.
Lemma weakUntil_until_or (φ ψ : t) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Lemma until_eventually_weakUntil (φ ψ : t) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Lemma expand_weakUntil  (φ ψ : t) : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).

(*** Release R *)

Notation "p 'R' q" := (release p q) (at level 45, right associativity).

Hypothesis release_def : forall (φ ψ : t), φ R ψ ≈ ¬ (¬ φ U ¬ ψ).

Lemma law_268 (φ ψ : t) : φ R ψ ≈ ¬(¬ φ U ¬ ψ).
Lemma law_269 (φ ψ : t) : φ U ψ ≈ ¬(¬ φ R ¬ ψ).
Lemma law_270 (φ ψ : t) : φ W ψ ≈ ψ R (ψ ∨ φ).
Lemma law_271 (φ ψ : t) : φ R ψ ≈ ψ W (ψ ∧ φ).
Lemma law_272 (φ ψ : t) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).
Lemma law_273 (φ ψ χ : t) : φ R (ψ ∨ χ) ≈ (φ R ψ) ∨ (φ R χ). (* ??? *)
Lemma law_274 (φ ψ χ : t) : (φ ∧ ψ) R χ ≈ (φ R χ) ∧ (ψ R χ). (* ??? *)
Lemma law_275 (φ ψ : t) : ◯ (φ R ψ) ≈ (◯ φ) R (◯ ψ).
Lemma law_276 (φ ψ : t) : □ ψ ≈ ⊥ R ψ.
Lemma not_until (φ ψ : t) : ¬ (φ U ψ) ≈ ¬φ R ¬ψ.
Lemma not_release (φ ψ : t) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Lemma always_release (ψ : t) : □ ψ ≈ ⊥ R ψ.
Lemma release_until (φ ψ : t) : φ R ψ ≈ ¬(¬φ U ¬ψ).
Lemma weakUntil_release_or (φ ψ : t) : φ W ψ ≈ ψ R (ψ ∨ φ).
Lemma release_weakUntil_and (φ ψ : t) : φ R ψ ≈ ψ W (ψ ∧ φ).
Lemma next_release (φ ψ : t) : ◯ (φ R ψ) ≈ (◯ φ) R (◯ ψ).
Lemma release_or (ρ φ ψ : t) : ρ R (φ ∨ ψ) ≈ (ρ R φ) ∨ (ρ R ψ).
Lemma and_release (ρ φ ψ : t) : (φ ∧ ψ) R ρ ≈ (φ R ρ) ∧ (ψ R ρ).
Lemma expand_release (φ ψ : t) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).

(*** Strong Release M *)

Notation "p 'M' q" := (strong_release p q) (at level 45, right associativity).

Hypothesis strong_release_def : forall (φ ψ : t), φ M ψ ≈ (φ R ψ) ∧ ◇ φ.

Lemma law_277 (φ ψ : t) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Lemma law_278 (φ ψ : t) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Lemma law_279 (φ ψ : t) : ¬(φ W ψ) ≈ (¬ φ M ¬ ψ).
Lemma law_280 (φ ψ : t) : ¬(φ M ψ) ≈ (¬ φ W ¬ ψ).
Lemma not_weakUntil (φ ψ : t) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Lemma not_strongRelease (φ ψ : t) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Lemma strongRelease_not_weakUntil (φ ψ : t) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Lemma strongRelease_and_release (φ ψ : t) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Lemma strongRelease_release_and (φ ψ : t) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).

(*** OLD *)

Notation "p ≉ q" := (~ (p ≈ q)) (at level 90, no associativity).

Lemma law_34 (φ : t) : ◇□ φ ⟹ □◇ φ.
Lemma law_35 (φ : t) : □¬ φ ⟹ ¬□ φ.
Lemma law_43 (φ : t) : ◇□◇ φ ≈ □◇ φ.
Lemma law_44 (φ : t) : □◇□ φ ≈ ◇□ φ.
Lemma law_45 (φ : t) : □◇□◇ φ ≈ □◇ φ.
Lemma law_46 (φ : t) : ◇□◇□ φ ≈ ◇□ φ.
Lemma law_47 (φ : t) : ◯□◇ φ ≈ □◇ φ.
Lemma law_48 (φ : t) : ◯◇□ φ ≈ ◇□ φ.
Lemma law_53 (φ ψ : t) : □ (φ ∧ ψ) ≈ □ φ ∧ □ ψ.
Lemma law_54 (φ ψ : t) : □ (φ ∨ ψ) ≉ □ φ ∨ □ ψ.
Lemma law_57 (φ ψ : t) : ◇ (φ ∧ ψ) ≉ ◇ φ ∧ ◇ ψ.
Lemma law_58 (φ ψ : t) : ◇ (φ ∨ ψ) ≈ ◇ φ ∨ ◇ ψ.
Lemma law_63 (φ ψ : t) : ◇□ (φ ∧ ψ) ≈ ◇□ φ ∧ ◇□ ψ.
Lemma law_64 (φ ψ : t) : □◇ (φ ∨ ψ) ≈ □◇ φ ∨ □◇ ψ.
Lemma law_65 (φ ψ : t) : ◇□ (φ → □ ψ) ≈ ◇□¬ φ ∧ ◇□ ψ.
Lemma law_66 (φ ψ : t) : □ (□◇ φ → ◇ ψ) ≈ ◇□¬ φ ∧ □◇ ψ.
Lemma law_67 (φ ψ : t) : □ ((φ ∨ □ ψ) ∧ (□ φ ∨ ψ)) ≈ □ φ ∨ □ ψ.
Lemma law_70 (φ : t) : ◇ φ ∧ □¬ φ ≈ ⊥.
Lemma law_71 (φ : t) : □ φ ∧ ◇¬ φ ≈ ⊥.
Lemma law_72 (φ : t) : □ φ ∧ □¬ φ ≈ ⊥.
Lemma law_73 (φ : t) : □◇ φ ∧ ◇□¬ φ ≈ ⊥.
Lemma law_74 (φ : t) : ◇□ φ ∧ □◇¬ φ ≈ ⊥.
Lemma law_75 (φ : t) : ◇□ φ ∧ ◇□¬ φ ≈ ⊥.
Lemma law_76 (φ : t) : ◇ φ ∨ □¬ φ ≈ ⊤.
Lemma law_77 (φ : t) : □ φ ∨ ◇¬ φ ≈ ⊤.
Lemma law_78 (φ : t) : ◇ φ ∨ ◇¬ φ ≈ ⊤.
Lemma law_79 (φ : t) : □◇ φ ∨ ◇□¬ φ ≈ ⊤.
Lemma law_80 (φ : t) : □◇ φ ∨ □◇¬ φ ≈ ⊤.
Lemma law_81 (φ : t) : ◇□ φ ∨ □◇¬ φ ≈ ⊤.
Lemma law_82 (φ ψ : t) : ◇ (φ → ψ) ⟹ □ φ → ◇ ψ.
Lemma law_85 (φ ψ : t) : □ (φ → ψ) ⟹ □ φ → □ ψ.
Lemma law_86 (φ ψ : t) : □ φ ∨ □ ψ ⟹ □ (φ ∨ ψ).
Lemma law_87 (φ ψ : t) : □ φ ∧ ◇ ψ ⟹ ◇ (φ ∧ ψ).
Lemma law_88 (φ ψ : t) : ◇ φ → ◇ ψ ⟹ ◇ (φ → ψ).
Lemma law_90 (φ ψ : t) : □◇ (φ ∧ ψ) ⟹ □◇ φ ∧ □◇ ψ.
Lemma law_91 (φ ψ : t) : □◇ (φ ∨ ψ) ⟹ □◇ φ ∨ □◇ ψ.
Lemma law_92 (φ ψ : t) : ◇□ (φ ∧ ψ) ⟹ ◇□ φ ∧ ◇□ ψ.
Lemma law_93 (φ ψ : t) : ◇□ φ ∨ ◇□ ψ ⟹ ◇□ (φ ∨ ψ).
Lemma law_94 (φ ψ : t) : ◇□ φ ∧ □◇ ψ ⟹ □◇ (φ ∧ ψ).
Lemma law_95 (φ ψ : t) : ◇□ φ ∧ □ (□ φ → ◇ ψ) ⟹ ◇ ψ.
Lemma law_96 (φ ψ : t) : □ (φ → ψ) ⟹ ◯ φ → ◯ ψ.
Lemma law_97 (φ ψ : t) : □ (φ → ψ) ⟹ ◇ φ → ◇ ψ.
Lemma law_98 (φ ψ : t) : □ (φ → ψ) ⟹ □◇ φ → □◇ ψ.
Lemma law_99 (φ ψ : t) : □ (φ → ψ) ⟹ ◇□ φ → ◇□ ψ.
Lemma law_100 (φ ψ : t) : □ φ ⟹ ◯ ψ → ◯ (φ ∧ ψ).
Lemma law_101 (φ ψ : t) : □ φ ⟹ ◇ ψ → ◇ (φ ∧ ψ).
Lemma law_102 (φ ψ : t) : □ φ ⟹ □ ψ → □ (φ ∧ ψ).
Lemma law_103 (φ ψ : t) : □ φ ⟹ ◯ ψ → ◯ (φ ∨ ψ).
Lemma law_104 (φ ψ : t) : □ φ ⟹ ◇ ψ → ◇ (φ ∨ ψ).
Lemma law_105 (φ ψ : t) : □ φ ⟹ □ ψ → □ (φ ∨ ψ).
Lemma law_106 (φ ψ : t) : □ φ ⟹ ◯ ψ → ◯ (φ → ψ).
Lemma law_107 (φ ψ : t) : □ φ ⟹ ◇ ψ → ◇ (φ → ψ).
Lemma law_108 (φ ψ : t) : □ φ ⟹ □ ψ → □ (φ → ψ).
Lemma law_109 (φ ψ : t) : □ (□ φ → ψ) ⟹ □ φ → □ ψ.
Lemma law_110 (φ ψ : t) : □ (φ → ◇ψ) ⟹ ◇ φ → ◇ ψ.
Lemma law_112 (φ ψ : t) : □ (φ → ◯ ψ) ⟹ φ → ◇ ψ.
Lemma law_113 (φ : t) : □ (φ → ◯¬ φ) ⟹ φ → ¬□ φ.
Lemma law_115 (φ ψ : t) : □ (φ ∨ ◯ ψ → ψ) ⟹ ◇ φ → ψ.
Lemma law_116 (φ ψ : t) : □ (φ → ◯ φ ∧ ψ) ⟹ φ → □ ψ.
Lemma law_117 (φ ψ χ : t) : □ (φ → (◯ φ ∧ ψ) ∨ χ) ⟹ φ → □ ψ ∨ (ψ U χ).
Lemma law_118 (φ ψ : t) : □ (φ → ◯ (φ ∨ ψ)) ⟹ φ → □ φ ∨ (φ U ψ).
Lemma law_119 (φ ψ χ ρ : t) : □ ((φ → ψ) ∧ (ψ → ◯ χ) ∧ (χ → ρ)) ⟹ φ → ◯ ρ.
Lemma law_120 (φ ψ χ ρ : t) : □ ((φ → ψ) ∧ (ψ → ◇ χ) ∧ (χ → ρ)) ⟹ φ → ◇ ρ.
Lemma law_121 (φ ψ χ ρ : t) : □ ((φ → ψ) ∧ (ψ → □ χ) ∧ (χ → ρ)) ⟹ φ → □ ρ.
Lemma law_122 (φ ψ χ : t) : □ ((φ → ◇ ψ) ∧ (ψ → ◇ χ)) ⟹ φ → ◇ χ.
Lemma law_123 (φ ψ χ : t) : □ ((φ → □ ψ) ∧ (ψ → □ χ)) ⟹ φ → □ χ.
Lemma law_124 (φ ψ χ : t) : (□ (□ φ → ◇ ψ) ∧ (ψ → ◯ χ)) ⟹ □ φ → ◯□◇ χ.
Lemma law_125 (φ ψ : t) : □ (φ ∨ ψ) ≈ ⊤ -> exists u, □ ((φ ∧ u) ∨ (ψ ∧ ¬ u)) ≈ ⊤.
Lemma law_126 (φ ψ χ ρ : t) : □ ((φ → ◇ (ψ ∨ χ)) ∧ (ψ → ◇ ρ) ∧ (χ → ◇ ρ)) ⟹ φ → ◇ ρ.
Lemma law_127 (φ ψ : t) : □ (□ φ → ψ) ∨ □ (□ ψ → φ) ≈ ⊤.
Lemma law_128 (φ : t) : φ U ⊥ ≈ ⊥.
Lemma law_132 (φ : t) : ¬ φ U φ ≈ ◇ φ.
Lemma law_136 (φ ψ : t) : (φ U ψ) ∨ (φ U ¬ ψ) ≈ ⊤.
Lemma law_145 (φ ψ : t) : φ U ψ ≈ (φ ∨ ψ) U ψ.
Lemma law_146 (φ ψ : t) : φ U ψ ≈ (φ ∧ ¬ ψ) U ψ.
Lemma law_148 (φ ψ χ : t) : (φ U χ) ∨ (ψ U χ) ⟹ (φ ∨ ψ) U χ.
Lemma law_150 (φ ψ χ : t) : φ U (ψ ∧ χ) ⟹ (φ U ψ) ∧ (φ U χ).
Lemma law_151 (φ ψ χ : t) : φ U (ψ ∧ χ) ⟹ φ U (ψ U χ).
Lemma law_152 (φ ψ χ : t) : (φ ∧ ψ) U χ ⟹ (φ U ψ) U χ.
Lemma law_153 (φ ψ χ : t) : (φ ∧ ψ) U χ ⟹ φ U (ψ U χ).
Lemma law_155 (φ ψ : t) : ◇ (φ U ψ) ≉ (◇ φ) U (◇ ψ).
Lemma law_160 (φ : t) : φ U □ φ ≈ □ φ.
Lemma law_161 (φ ψ : t) : φ U □ ψ ≈ □ (φ U ψ).
Lemma law_162 (φ ψ : t) : ◇ φ ⟹ ((φ → ψ) U φ).
Lemma law_170 (φ ψ : t) : □ φ ⟹ ◯ ψ → ◯ (φ U ψ).
Lemma law_171 (φ ψ : t) : □ φ ⟹ ◇ ψ → ◇ (φ U ψ).
Lemma law_172 (φ ψ : t) : □ φ ⟹ □ ψ → □ (φ U ψ).
Lemma law_174 (φ ψ : t) : □ φ ⟹ ◇ ψ → φ U ψ.
Lemma law_176 (φ ψ χ : t) : □ (φ → ψ) ⟹ (χ U φ) → (χ U ψ).
Lemma law_177 (φ ψ χ : t) : □ (φ → ψ) ⟹ (φ U χ) → (ψ U χ).
Lemma law_179 (φ ψ χ ρ : t) : □ ((φ → ψ U χ) ∧ (χ → ψ U ρ)) ⟹ φ → □ χ.
Lemma law_180 (φ ψ χ ρ : t) : □ ((φ → χ) ∧ (ψ → ρ)) ⟹ φ U ψ → χ U ρ.
Lemma law_181 (φ ψ χ : t) : □ (φ → ¬ ψ ∧ ◯ χ) ⟹ φ → ¬ (ψ U χ).
Lemma eventually_always_until (φ ψ : t) : ◇ ψ ⟹ □ φ → φ U ψ.

(* Definition examine {a : Type} (P : a -> t) : t := fun s => P (head s) s. *)

End LinearTemporalLogic.
