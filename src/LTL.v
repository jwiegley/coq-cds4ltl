Set Warnings "-local-declaration".

Require Import
  Coq.micromega.Lia
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid
  MinLTL.

Module Type LinearTemporalLogic <: MinimalLinearTemporalLogic.

Include MinimalLinearTemporalLogic.

Parameter eventually : t -> t.
Parameter always : t -> t.
Parameter wait : t -> t -> t.
(* Parameter release : t -> t -> t. *)
(* Parameter strong_release : t -> t -> t. *)

Notation "◇ p"     := (eventually p)       (at level 75, right associativity) : ltl_scope.
Notation "□ p"     := (always p)           (at level 75, right associativity) : ltl_scope.
Notation "p 'W' q" := (wait p q)           (at level 79, right associativity) : ltl_scope.
(* Notation "p 'R' q" := (release p q)        (at level 79, right associativity) : ltl_scope. *)
(* Notation "p 'M' q" := (strong_release p q) (at level 79, right associativity) : ltl_scope. *)

Declare Instance eventually_respects_implies :
  Proper (implies ==> implies) eventually.
Declare Instance always_respects_implies :
  Proper (implies ==> implies) always.
Declare Instance wait_respects_implies :
  Proper (implies ==> implies ==> implies) wait.
(* Declare Instance release_respects_implies : *)
(*   Proper (implies ==> implies ==> implies) release. *)
(* Declare Instance strong_release_respects_implies : *)
(*   Proper (implies ==> implies ==> implies) strong_release. *)

Axiom (* 38 *) evn_def : forall (p : t), ◇ p ≈ ⊤ U p.
Axiom (* 54 *) always_def : forall (p : t), □ p ≈ ¬◇ ¬p.
Axiom (* 169 *) wait_def : forall (p q : t), p W q ≈ □ p ∨ p U q.
(* Axiom release_def : forall (p q : t), p R q ≈ ¬(¬p U ¬q). *)
(* Axiom strong_release_def : forall (p q : t), p M q ≈ p U (q ∧ p). *)

Axiom (* 55 *) always_until_and_ind : forall (p q r : t),
  □ (p ⇒ (◯ p ∧ q) ∨ r) ⟹ p ⇒ □ q ∨ q U r.

Parameter holds : nat -> t -> t.

Infix "⊨" := holds (at level 87, no associativity) : ltl_scope.

Declare Instance holds_respects_implies :
  Proper (eq ==> implies ==> implies) holds.

(** In order prove meta-theorems concerning the facts of temporality, we
    require a semantics to express how "the flow of time" relates to the
    boolean and temporal operators. *)
(* Axiom impl_holds   : forall p q j, j ⊨ p ⇒ q <-> (j ⊨ p -> j ⊨ q). *)
(* Axiom always_holds : forall p j, j ⊨ □ p <-> forall i, i >= j -> i ⊨ p. *)

End LinearTemporalLogic.

Module LinearTemporalLogicFacts (L : LinearTemporalLogic).

Import L.
Module Import MLTL := MinimalLinearTemporalLogicFacts L.
Module Import BF := MLTL.BF.
Module Import MBF := BF.MBF.

Program Instance eventually_respects_equivalent :
  Proper (equivalent ==> equivalent) eventually.
Program Instance always_respects_equivalent :
  Proper (equivalent ==> equivalent) always.
Program Instance wait_respects_equivalent :
  Proper (equivalent ==> equivalent ==> equivalent) wait.
(* Program Instance release_respects_equivalent : *)
(*   Proper (equivalent ==> equivalent ==> equivalent) release. *)
(* Program Instance strong_release_respects_equivalent : *)
(*   Proper (equivalent ==> equivalent ==> equivalent) strong_release. *)

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

Theorem (* 39 *) law_39 (p q : t) : (p U q) ∧ ◇ q ≈ p U q.
Proof.
  rewrite evn_def.
  rewrite <- until_right_and.
  now rewrite and_true.
Qed.

Theorem (* 40 *) until_absorb_or_evn (p q : t) : (p U q) ∨ ◇ q ≈ ◇ q.
Proof.
  rewrite evn_def.
  split.
  - rewrite until_right_or.
    now rewrite or_true.
  - rewrite or_comm.
    now apply or_inj.
Qed.

Theorem (* 41 *) until_absorb_evn (p q : t) : p U ◇ q ≈ ◇ q.
Proof.
  rewrite evn_def.
  split.
  - rewrite until_right_or_order.
    now rewrite or_true.
  - now apply until_insertion.
Qed.

Theorem (* 42 *) law_42 (p q : t) : p U q ⟹ ◇ q.
Proof.
  rewrite <- (until_absorb_evn p).
  apply until_respects_implies; [reflexivity|].
  rewrite evn_def.
  now rewrite <- until_insertion.
Qed.

Theorem (* 43 *) law_43 : ◇ ⊤ ≈ ⊤.
Proof.
  rewrite evn_def.
  now apply until_true.
Qed.

Theorem (* 44 *) law_44 : ◇ ⊥ ≈ ⊥.
Proof.
  rewrite evn_def.
  now apply until_right_bottom.
Qed.

Theorem (* 45 *) law_45 (p : t) : ◇ p ≈ p ∨ ◯ ◇ p.
Proof.
  rewrite evn_def at 1.
  rewrite until_expansion at 1.
  rewrite <- evn_def at 1.
  now rewrite true_and.
Qed.

Theorem (* 46 *) evn_weaken (p : t) : p ⟹ ◇ p.
Proof.
  rewrite evn_def.
  now rewrite <- until_insertion.
Qed.

Theorem (* 47 *) law_47 (p : t) : ◯ p ⟹ ◇ p.
Proof.
  rewrite evn_def.
  rewrite until_expansion.
  rewrite or_comm.
  rewrite <- or_inj.
  rewrite true_and.
  apply next_respects_implies.
  rewrite <- evn_def.
  apply evn_weaken.
Qed.

Theorem (* 48 *) law_48 (p : t) : p ∨ ◇ p ≈ ◇ p.
Proof.
  rewrite <- (false_until p) at 1.
  now apply until_absorb_or_evn.
Qed.

Theorem (* 49 *) law_49 (p : t) : ◇ p ∧ p ≈ p.
Proof.
  rewrite evn_def.
  now apply until_absorb_u_and.
Qed.

Theorem (* 50 *) law_50 (p : t) : ◇ ◇ p ≈ ◇ p.
Proof.
  rewrite !evn_def.
  now apply until_left_absorb.
Qed.

Theorem (* 51 *) law_51 (p : t) : ◯ ◇ p ≈ ◇ ◯ p.
Proof.
  rewrite !evn_def.
  rewrite next_until.
  now rewrite next_true.
Qed.

Theorem (* 52 *) evn_or (p q : t) : ◇ (p ∨ q) ≈ ◇ p ∨ ◇ q.
Proof.
  rewrite !evn_def.
  now apply until_left_or.
Qed.

Theorem (* 53 *) law_53 (p q : t) : ◇ (p ∧ q) ⟹ ◇ p ∧ ◇ q.
Proof.
  rewrite !evn_def.
  now apply until_left_and.
Qed.

(*** 3.4 Always □ *)

(**
(54) Definition of □ : □ p ≡ ¬◇ ¬p
(55) Axiom, U Induction : □ (p ⇒ (◯ p ∧ q) ∨ r) ⇒ (p ⇒ □ q ∨ q U r)
(56) Axiom, U Induction : □ (p ⇒ ◯ (p ∨ q)) ⇒ (p ⇒ □ p ∨ p U q)
(57) □ Induction: □ (p ⇒ ◯ p) ⇒ (p ⇒ □ p)
(58) ◇ Induction: □ (◯ p ⇒ p) ⇒ (◇ p ⇒ p)
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
(74) p ⇒ □ p ≡ p ⇒ ◯ □ p
(75) p ∧ ◇ ¬p ⇒ ◇ (p ∧ ◯ ¬p)
(76) Strengthening of □ : □ p ⇒ p
(77) Strengthening of □ : □ p ⇒ ◇ p
(78) Strengthening of □ : □ p ⇒ ◯ p
(79) Strengthening of □ : □ p ⇒ ◯ □
(80) ◯ generalization: □ p ⇒ □ ◯ p
(81) □ p ⇒ ¬(q U ¬p)
*)

Lemma until_impl : forall p q r : t, (p ⇒ r) ∧ (q ⇒ r) ⟹ (p U q ⇒ r).
Proof.
  intros.
  rewrite or_respects.
  rewrite until_28.
  now rewrite or_idem.
Qed.

Theorem (* 99 *) law_99_early (p q : t) : □ (p ∧ q) ≈ □ p ∧ □ q.
Proof.
  rewrite !always_def.
  rewrite not_and.
  rewrite evn_or.
  now rewrite not_or.
Qed.

Theorem (* 76 *) law_76_early (p : t) : □ p ⟹ p.
Proof.
  rewrite always_def.
  apply contrapositive.
  rewrite not_not.
  now apply evn_weaken.
Qed.

Corollary (* NEW *) always_apply_early (p q : t) : □ (p ⇒ q) ∧ p ⟹ q.
Proof.
  rewrite law_76_early.
  rewrite and_comm.
  rewrite and_apply.
  now boolean.
Qed.

Theorem (* 73 *) law_73_early (p : t) : ◯ □ p ≈ □ ◯ p.
Proof.
  rewrite !always_def.
  rewrite next_not.
  rewrite law_51.
  now rewrite <- next_not.
Qed.

Theorem (* 66 *) law_66_early (p : t) : □ p ≈ p ∧ ◯ □ p.
Proof.
  rewrite always_def.
  rewrite law_45 at 1.
  rewrite not_or.
  rewrite not_not.
  now rewrite next_not.
Qed.

(** Metatheorem U : If P ⇒ R is a theorem and Q ⇒ S is a theorem then
      P U Q ⇒ R U S
    is a theorem. *)
Lemma until_respects (p q r s : t) : (p ⇒ r) ∧ (q ⇒ s) ⟹ (p U q ⇒ r U s).
Proof.
Abort.

Theorem (* 61 *) law_61_early (p : t) : ¬◇ p ≈ □ ¬p.
Proof. now rewrite always_def; boolean. Qed.

Theorem (* 55 *) always_until_and_ind : forall (p q r : t),
  □ (p ⇒ (◯ p ∧ q) ∨ r) ⟹ p ⇒ □ q ∨ q U r.
Proof.
  intros.
  rewrite !always_def.
  apply contrapositive.
  (* rewrite !impl_def. *)
  rewrite !not_or.
  rewrite !not_and.
  rewrite !not_not.
  rewrite !evn_def.
  rewrite not_until.
  rewrite (and_comm p (and _ (¬r))).
  rewrite and_assoc.
  rewrite and_or_r.
  rewrite (* 12 *) until_left_or.
  rewrite <- !and_assoc.
  rewrite !(and_comm _ p).
  rewrite or_comm.
  rewrite <- or_inj.
  apply impl_implies; intros.
  (* rewrite impl_def. *)
  rewrite not_and.
  rewrite and_def.
  rewrite !not_not.
  rewrite not_or.
  rewrite (* AXIOM *) <- not_until.
  rewrite or_assoc.
  rewrite not_and.
  rewrite not_not.
  rewrite or_comm.
  rewrite or_assoc.
  rewrite (or_comm (not _)).
  rewrite or_assoc.
  rewrite <- (or_assoc _ _ (¬p)).
  rewrite <- !evn_def.

(*
  enough (forall (p q : t), □ (p ⇒ q) ⟹ (◇ p ⇒ ◇ q)).
    (* rewrite <- impl_def. *)
    rewrite <- and_assoc.
    rewrite (and_comm p).
    rewrite and_assoc.
    rewrite <- H.
    assert (forall x y, x ⇒ x ∧ y ≈ x ⇒ y).
      intros.
      boolean.
      rewrite or_and.
      now boolean.
    rewrite H0.
    rewrite law_61_early.
    (* rewrite !impl_def. *)
    rewrite !not_not.
    rewrite always_def.
    rewrite and_def.
    rewrite not_not.
    rewrite !not_or.
    (* rewrite impl_def. *)
    rewrite not_or.
    rewrite not_and.
    rewrite !not_not.
    rewrite <- or_assoc.
    rewrite (or_comm (q U r)).
    rewrite or_assoc.
    (* rewrite <- !impl_def. *)
    apply and_impl_iff.
    boolean.
    rewrite law_45.
    rewrite or_and_r.
    rewrite and_proj_r.
    rewrite until_30.

  enough (forall (p q : t), □ (p ⇒ q) ⟹ (◇ p ⇒ ◇ q)).
    (* rewrite <- impl_def. *)
    rewrite <- H.
    (* rewrite impl_def. *)
    rewrite not_not.
    rewrite <- and_assoc.
    rewrite (and_comm p).
    rewrite and_assoc.
    rewrite or_and.
    boolean.
    rewrite or_and.
    rewrite always_def.
    rewrite and_def.
    rewrite not_not.
    rewrite !not_or.
    rewrite <- or_assoc.
    rewrite (or_comm (q U r)).
    rewrite or_assoc.
    (* rewrite <- impl_def. *)
    apply and_impl_iff.
    boolean.
    rewrite <- and_or.
    rewrite (or_comm (q U r)).
    rewrite and_or.
    rewrite and_proj_r.
    (* rewrite <- !impl_def. *)
    apply and_impl_iff.
*)

  rewrite <- !always_def.
  rewrite <- evn_weaken.
  rewrite !or_assoc.
  rewrite <- (or_assoc _ _ (¬p)).
  rewrite or_and.
  rewrite or_and.
  boolean.
  rewrite <- or_and.
  rewrite <- or_and.
  rewrite or_assoc.
  rewrite or_and_r.
  boolean.
  rewrite (or_comm _ (¬p)).
  rewrite <- !or_assoc.
  rewrite or_comm.
  rewrite and_def.
  (* rewrite <- !impl_def. *)
  apply and_impl_iff.
  boolean.
  rewrite <- (or_inj _ (¬p)).
  rewrite (or_comm _ (□ q)).
  rewrite <- (* 29 *) until_insertion.
Abort.

Theorem (* 56 *) always_until_or_ind (p q : t) :
  □ (p ⇒ ◯ (p ∨ q)) ⟹ p ⇒ □ p ∨ p U q.
Proof.
  apply impl_implies.
  set (consequent := □ (p ⇒ ◯ (p ∨ q)) ⇒ p ⇒ □ p ∨ p U q).

  pose proof (always_until_and_ind p (◯ p) (◯ q)) as law_55.
  apply impl_implies in law_55.
  rewrite law_55.

  rewrite and_idem.
  rewrite (* 4 *) <- next_or.

  rewrite <- (true_and (p ⇒ _ ∨ _)).
  rewrite <- (impl_refl p).
  (* rewrite !impl_def. *)
  rewrite <- or_and.
  rewrite and_or.
  rewrite (or_inj (p ∧ _ U _) q).
  rewrite (or_comm (p ∧ _ U _) q).

  rewrite (* 9 *) <- next_until.
  rewrite (* 10 *) <- (until_expansion p q).
  rewrite (* 73 *) <- law_73_early.
  rewrite (* 66 *) <- (law_66_early p).
  (* rewrite <- !impl_def. *)
  reflexivity.
Qed.

Theorem (* 57 *) always_induction (p : t) : □ (p ⇒ ◯ p) ⟹ (p ⇒ □ p).
Proof.
  pose proof (always_until_or_ind p ⊥).
  rewrite or_false in H.
  rewrite H.
  rewrite until_right_bottom.
  now rewrite or_false.
Qed.

Lemma (* 58 *) evn_induction (p : t) : □ (◯ p ⇒ p) ⟹ (◇ p ⇒ p).
Proof.
  apply impl_implies.
  set (consequent := □ (◯ p ⇒ p) ⇒ ◇ p ⇒ p).

  pose proof (always_until_or_ind (¬ p) ⊥) as law_56.
  apply impl_implies in law_56.
  rewrite law_56.

  rewrite until_right_bottom.
  rewrite !or_false.
  rewrite next_linearity.
  (* rewrite !impl_def. *)
  rewrite !not_not.
  rewrite !(or_comm p).
  rewrite (always_def (¬p)).
  rewrite not_not.
  (* rewrite <- !impl_def. *)
  reflexivity.
Qed.

Theorem (* 59 *) law_59 (p : t) : ◇ p ≈ ¬□ ¬p.
Proof. now rewrite always_def; boolean. Qed.

Theorem (* 60 *) law_60 (p : t) : ¬□ p ≈ ◇ ¬p.
Proof. now rewrite always_def; boolean. Qed.

Theorem (* 61 *) law_61 (p : t) : ¬◇ p ≈ □ ¬p.
Proof. now rewrite always_def; boolean. Qed.

Theorem (* 62 *) law_62 (p : t) : ¬◇ □ p ≈ □ ◇ ¬p.
Proof. now rewrite !always_def. Qed.

Theorem (* 63 *) law_63 (p : t) : ¬□ ◇ p ≈ ◇ □ ¬p.
Proof. now rewrite !always_def; boolean. Qed.

Theorem (* 64 *) law_64 : □ ⊤ ≈ ⊤.
Proof.
  rewrite always_def.
  rewrite not_true.
  rewrite law_44.
  now rewrite not_false.
Qed.

Theorem (* 65 *) law_65 : □ ⊥ ≈ ⊥.
Proof.
  rewrite always_def.
  rewrite not_false.
  rewrite law_43.
  now rewrite not_true.
Qed.

Theorem (* 66 *) law_66 (p : t) : □ p ≈ p ∧ ◯ □ p.
Proof.
  rewrite always_def.
  rewrite law_45 at 1.
  rewrite not_or.
  rewrite not_not.
  now rewrite next_not.
Qed.

Theorem (* 67 *) law_67 (p : t) : □ p ≈ p ∧ ◯ p ∧ ◯ □ p.
Proof.
  split.
  - rewrite <- next_and.
    assert (□ p ⟹ p ∧ □ p).
      rewrite law_66.
      rewrite <- and_assoc.
      now rewrite and_idem.
    rewrite <- H.
    now apply law_66.
  - rewrite <- and_assoc.
    rewrite (and_comm p).
    rewrite and_assoc.
    rewrite <- law_66.
    rewrite and_comm.
    now apply and_proj.
Qed.

Theorem (* 68 *) law_68 (p : t) : p ∧ □ p ≈ □ p.
Proof.
  split.
  - rewrite always_def.
    rewrite and_comm.
    now apply and_proj.
  - rewrite law_66.
    rewrite <- and_assoc.
    now rewrite and_idem.
Qed.

Theorem (* 69 *) law_69 (p : t) : □ p ∨ p ≈ p.
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

Theorem (* 70 *) law_70 (p : t) : ◇ p ∧ □ p ≈ □ p.
Proof.
  split.
  - rewrite and_comm.
    now apply and_proj.
  - rewrite <- law_68 at 1.
    now rewrite <- evn_weaken.
Qed.

Theorem (* 71 *) law_71 (p : t) : □ p ∨ ◇ p ≈ ◇ p.
Proof.
  split.
  - rewrite always_def.
    apply contrapositive.
    rewrite <- (evn_weaken (¬ p)).
    rewrite not_not.
    now rewrite law_48.
  - rewrite or_comm.
    now apply or_inj.
Qed.

Theorem (* 72 *) law_72 (p : t) : □ □ p ≈ □ p.
Proof.
  rewrite always_def.
  rewrite law_60.
  rewrite law_50.
  now rewrite <- always_def.
Qed.

Theorem (* 73 *) law_73 (p : t) : ◯ □ p ≈ □ ◯ p.
Proof.
  rewrite !always_def.
  rewrite next_not.
  rewrite law_51.
  now rewrite <- next_not.
Qed.

Theorem (* 74 *) law_74 (p : t) : p ⇒ □ p ⟹ p ⇒ ◯ □ p.
Proof.
  rewrite always_def.
  rewrite <- always_def.
  rewrite law_66 at 1.
  (* rewrite !impl_def. *)
  rewrite or_and.
  rewrite or_comm at 1.
  rewrite true_def.
  now rewrite true_and.
Qed.

Theorem (* 75 *) law_75 (p : t) : p ∧ ◇ ¬p ⟹ ◇ (p ∧ ◯ ¬p).
Proof.
  apply contrapositive.
  rewrite !and_def.
  rewrite <- !always_def.
  rewrite next_not.
  rewrite !not_not.
  (* rewrite <- !impl_def. *)
  now apply always_induction.
Qed.

Theorem (* 76 *) law_76 (p : t) : □ p ⟹ p.
Proof.
  rewrite always_def.
  apply contrapositive.
  rewrite not_not.
  now apply evn_weaken.
Qed.

Corollary (* NEW *) always_apply (p q : t) : □ (p ⇒ q) ∧ p ⟹ q.
Proof.
  rewrite law_76.
  rewrite and_comm.
  rewrite and_apply.
  now boolean.
Qed.

Theorem (* 77 *) law_77 (p : t) : □ p ⟹ ◇ p.
Proof.
  rewrite <- evn_weaken.
  now apply law_76.
Qed.

Theorem (* 78 *) law_78 (p : t) : □ p ⟹ ◯ p.
Proof.
  rewrite law_67.
  rewrite and_comm.
  rewrite and_proj.
  now apply and_proj.
Qed.

Theorem (* 79 *) law_79 (p : t) : □ p ⟹ ◯ □ p.
Proof.
  rewrite <- law_78.
  now rewrite law_72.
Qed.

Theorem (* 80 *) law_80 (p : t) : □ p ⟹ □ ◯ p.
Proof.
  rewrite <- law_73.
  now apply law_79.
Qed.

Theorem (* 81 *) law_81 (p q : t) : □ p ⟹ ¬(q U ¬p).
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
 *)

(*
Theorem (* 82 *) temporal_deduction (p q : t) j :
  (forall i, i >= j -> i ⊨ (⊤ ⇒ p) -> i ⊨ q) -> j ⊨ (□ p ⇒ q).
Proof.
  intros.
  apply (proj2 (impl_holds (□ p) q j)).
  intros.
  apply H.
    lia.
  pose proof (proj1 (always_holds p j) H0).
  apply impl_holds.
  intros.
  apply H1.
  lia.
Qed.
*)

Theorem (* 82 *) temporal_deduction (P₁ P₂ Q : t) :
  ((⊤ ⟹ P₁) -> (⊤ ⟹ P₂) -> (⊤ ⟹ Q)) -> (□ P₁ ∧ □ P₂ ⟹ Q).
Proof.
  intros.
  rewrite <- true_and.
  apply and_impl_iff.
  enough (P₁ ∧ P₂ ⟹ Q).
    apply impl_implies in H0.
    rewrite <- (true_or (□ P₁ ∧ □ P₂ ⇒ Q)).
    rewrite H0.
    rewrite <- and_impl.
    rewrite and_assoc.
    rewrite <- (and_assoc P₂).
    rewrite (and_comm P₂).
    rewrite and_assoc.
    rewrite law_68.
    rewrite <- and_assoc.
    rewrite law_68.
    reflexivity.
Admitted.

Theorem (* 82 *) temporal_deduction_simple (P₁ P₂ Q : t) :
  (P₁ ∧ P₂ ⟹ Q) -> (□ P₁ ∧ □ P₂ ⟹ Q).
Proof.
  intros.
  rewrite <- true_and.
  apply and_impl_iff.
  apply impl_implies in H.
  rewrite <- (true_or (□ P₁ ∧ □ P₂ ⇒ Q)).
  rewrite H.
  rewrite <- and_impl.
  rewrite and_assoc.
  rewrite <- (and_assoc P₂).
  rewrite (and_comm P₂).
  rewrite and_assoc.
  rewrite law_68.
  rewrite <- and_assoc.
  rewrite law_68.
  reflexivity.
Qed.

(*** 3.6 Always □, Continued *)

(**
(83) Distributivity of ∧ over U : □ p ∧ q U r ⇒ (p ∧ q) U (p ∧ r)
(84) U implication : □ p ∧ ◇ q ⇒ p U q
(85) Right monotonicity of U : □ (p ⇒ q) ⇒ (r U p ⇒ r U q)
(86) Left monotonicity of U : □ (p ⇒ q) ⇒ (p U r ⇒ q U r)
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
(104) Distributivity of ◇ over ⇒ : ◇ (p ⇒ q) ≡ (□ p ⇒ ◇ q)
(105) Distributivity of ◇ over ⇒ : (◇ p ⇒ ◇ q) ⇒ ◇ (p ⇒ q)
(106) ∧ frame law of ◯ : □ p ⇒ (◯ q ⇒ ◯ (p ∧ q))
(107) ∧ frame law of ◇ : □ p ⇒ (◇ q ⇒ ◇ (p ∧ q))
(108) ∧ frame law of □ : □ p ⇒ (□ q ⇒ □ (p ∧ q))
(109) ∨ frame law of ◯ : □ p ⇒ (◯ q ⇒ ◯ (p ∨ q))
(110) ∨ frame law of ◇ : □ p ⇒ (◇ q ⇒ ◇ (p ∨ q))
(111) ∨ frame law of □ : □ p ⇒ (□ q ⇒ □ (p ∨ q))
(112) ⇒ frame law of ◯ : □ p ⇒ (◯ q ⇒ ◯ (p ⇒ q))
(113) ⇒ frame law of ◇ : □ p ⇒ (◇ q ⇒ ◇ (p ⇒ q))
(114) ⇒ frame law of □ : □ p ⇒ (□ q ⇒ □ (p ⇒ q))
(115) ≡ frame law of ◯ : □ p ⇒ (◯ q ⇒ ◯ (p ≡ q))
(116) ≡ frame law of ◇ : □ p ⇒ (◇ q ⇒ ◇ (p ≡ q))
(117) ≡ frame law of □ : □ p ⇒ (□ q ⇒ □ (p ≡ q))
(118) Monotonicity of ◯ : □ (p ⇒ q) ⇒ (◯ p ⇒ ◯ q)
(119) Monotonicity of ◇ : □ (p ⇒ q) ⇒ (◇ p ⇒ ◇ q)
(120) Monotonicity of □ : □ (p ⇒ q) ⇒ (□ p ⇒ □ q)
(121) Consequence rule of ◯ : □ ((p ⇒ q) ∧ (q ⇒ ◯ r) ∧ (r ⇒ s)) ⇒ (p ⇒ ◯ s)
(122) Consequence rule of ◇ : □ ((p ⇒ q) ∧ (q ⇒ ◇ r) ∧ (r ⇒ s)) ⇒ (p ⇒ ◇ s)
(123) Consequence rule of □ : □ ((p ⇒ q) ∧ (q ⇒ □ r) ∧ (r ⇒ s)) ⇒ (p ⇒ □ s)
(124) Catenation rule of ◇ : □ ((p ⇒ ◇ q) ∧ (q ⇒ ◇ r)) ⇒ (p ⇒ ◇ r)
(125) Catenation rule of □ : □ ((p ⇒ □ q) ∧ (q ⇒ □ r)) ⇒ (p ⇒ □ r)
(126) Catenation rule of U : □ ((p ⇒ q U r) ∧ (r ⇒ q U s)) ⇒ (p ⇒ q U s)
(127) U strengthening rule: □ ((p ⇒ r) ∧ (q ⇒ s)) ⇒ (p U q ⇒ r U s)
(128) Induction rule ◇ : □ (p ∨ ◯ q ⇒ q) ⇒ (◇ p ⇒ q)
(129) Induction rule □ : □ (p ⇒ q ∧ ◯ p) ⇒ (p ⇒ □ q)
(130) Induction rule U : □ (p ⇒ ¬q ∧ ◯ p) ⇒ (p ⇒ ¬(r U q))
(131) ◇ Conﬂuence: □ ((p ⇒ ◇ (q ∨ r)) ∧ (q ⇒ ◇ t) ∧ (r ⇒ ◇ t)) ⇒ (p ⇒ ◇ t)
(132) Temporal generalization law : □ (□ p ⇒ q) ⇒ (□ p ⇒ □ q)
(133) Temporal particularization law : □ (p ⇒ ◇ q) ⇒ (◇ p ⇒ ◇ q)
(134) □ (p ⇒ ◯ q) ⇒ (p ⇒ ◇ q)
(135) □ (p ⇒ ◯ ¬p) ⇒ (p ⇒ ¬□ p)
*)

Theorem (* 83 *) law_83 (p q r : t) : □ p ∧ q U r ⟹ (p ∧ q) U (p ∧ r).
Proof.
  apply and_impl_iff.
  pose proof (temporal_deduction p ⊤).
  setoid_rewrite law_64 in H.
  setoid_rewrite and_true in H.
  apply H; intros.
  rewrite <- H0.
  now boolean.
Qed.

Theorem (* 84 *) law_84 (p q : t) : □ p ∧ ◇ q ⟹ p U q.
Proof.
  rewrite evn_def.
  rewrite law_83.
  rewrite and_true.
  rewrite until_left_and.
  now boolean.
Qed.

Corollary (* NEW *) law_84b (p q : t) : □ p ⟹ ◇ q ⇒ p U q.
Proof.
  apply and_impl_iff.
  now apply law_84.
Qed.

Corollary (* NEW *) law_84c (p q : t) : ¬(p U q) ⟹ ◇ q ⇒ ◇ ¬p.
Proof.
  apply contrapositive.
  (* rewrite impl_def. *)
  rewrite not_or.
  rewrite !not_not.
  rewrite <- always_def.
  rewrite and_comm.
  now apply law_84.
Qed.

Theorem (* 85 *) law_85 (p q r : t) : □ (p ⇒ q) ⟹ (r U p ⇒ r U q).
Proof.
  apply and_impl_iff.
  rewrite law_83.
  now apply until_respects_implies; boolean.
Qed.

Theorem (* 86 *) law_86 (p q r : t) : □ (p ⇒ q) ⟹ (p U r ⇒ q U r).
Proof.
  apply and_impl_iff.
  rewrite law_83.
  now apply until_respects_implies; boolean.
Qed.

Theorem (* 87 *) law_87 (p : t) : □ ¬p ⟹ ¬□ p.
Proof.
  rewrite !always_def.
  boolean.
  rewrite <- evn_weaken.
  now apply evn_weaken.
Qed.

Theorem (* 88 *) law_88 (p q : t) : □ p ∧ ◇ q ⟹ ◇ (p ∧ q).
Proof.
  rewrite !evn_def.
  rewrite law_83.
  boolean.
  now apply until_respects_implies; boolean.
Qed.

Theorem (* 89 *) law_89 (p : t) : ◇ p ∨ □ ¬p ≈ ⊤.
Proof.
  rewrite always_def.
  now boolean.
Qed.

Theorem (* 90 *) law_90 (p : t) : □ p ∨ ◇ ¬p ≈ ⊤.
Proof.
  rewrite always_def.
  now boolean.
Qed.

Theorem (* 91 *) law_91 (p : t) : ◇ p ∨ ◇ ¬p ≈ ⊤.
Proof.
  rewrite !evn_def.
  now apply until_excl_middle.
Qed.

Theorem (* 92 *) law_92 (p : t) : ◇ p ∧ □ ¬p ≈ ⊥.
Proof.
  rewrite always_def.
  now boolean.
Qed.

Theorem (* 93 *) law_93 (p : t) : □ p ∧ ◇ ¬p ≈ ⊥.
Proof.
  rewrite always_def.
  now boolean.
Qed.

Theorem (* 94 *) law_94 (p : t) : □ p ∧ □ ¬p ≈ ⊥.
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

Theorem (* 95 *) law_95 (p : t) : □ ◇ p ∨ ◇ □ ¬p ≈ ⊤.
Proof.
  rewrite <- law_63.
  now boolean.
Qed.

Theorem (* 96 *) law_96 (p : t) : ◇ □ p ∨ □ ◇ ¬p ≈ ⊤.
Proof.
  rewrite <- law_62.
  now boolean.
Qed.

Theorem (* 97 *) law_97 (p : t) : □ ◇ p ∧ ◇ □ ¬p ≈ ⊥.
Proof.
  rewrite <- law_63.
  now boolean.
Qed.

Theorem (* 98 *) law_98 (p : t) : ◇ □ p ∧ □ ◇ ¬p ≈ ⊥.
Proof.
  rewrite <- law_62.
  now boolean.
Qed.

Theorem (* 99 *) law_99 (p q : t) : □ (p ∧ q) ≈ □ p ∧ □ q.
Proof.
  rewrite !always_def.
  rewrite not_and.
  rewrite evn_or.
  now rewrite not_or.
Qed.

Theorem (* 100 *) law_100 (p q : t) : □ p ∨ □ q ⟹ □ (p ∨ q).
Proof.
  rewrite !always_def.
  apply contrapositive.
  rewrite not_or.
  rewrite !not_not.
  rewrite law_53.
  now rewrite <- and_def.
Qed.

Theorem (* 101 *) law_101 (p q : t) : □ (p ≡ q) ⟹ (◯ p ≡ ◯ q).
Proof.
  rewrite law_78.
  now rewrite next_eqv.
Qed.

Theorem (* 102 *) law_102 (p q : t) : □ (p ≡ q) ⟹ (◇ p ≡ ◇ q).
Proof.
  boolean.
  rewrite law_99.
  apply and_respects_implies.
    (* rewrite <- (impl_def (◇ p)). *)
    apply and_impl_iff.
    rewrite law_88.
    boolean.
    now rewrite and_proj_r.
  (* rewrite <- (impl_def (◇ q)). *)
  apply and_impl_iff.
  rewrite law_88.
  boolean.
  now rewrite and_proj_r.
Qed.

Theorem (* 103 *) law_103 (p q : t) : □ (p ≡ q) ⟹ (□ p ≡ □ q).
Proof.
  boolean.
  (* rewrite <- !impl_def. *)
  rewrite law_99.
  apply and_respects_implies;
  apply and_impl_iff.
    rewrite <- law_99.
    rewrite and_comm.
    rewrite and_apply.
    now rewrite and_proj_r.
  rewrite <- law_99.
  rewrite and_comm.
  rewrite and_apply.
  now rewrite and_proj_r.
Qed.

Theorem (* 104 *) law_104 (p q : t) : ◇ (p ⇒ q) ≈ (□ p ⇒ ◇ q).
Proof.
  (* rewrite !impl_def. *)
  rewrite evn_or.
  now rewrite law_60.
Qed.

Theorem (* 105 *) law_105 (p q : t) : (◇ p ⇒ ◇ q) ⟹ ◇ (p ⇒ q).
Proof.
  (* rewrite !impl_def. *)
  rewrite evn_or.
  rewrite <- law_60.
  rewrite law_61.
  now rewrite law_87.
Qed.

Theorem (* 106 *) law_106 (p q : t) : □ p ⟹ (◯ q ⇒ ◯ (p ∧ q)).
Proof.
  apply and_impl_iff.
  rewrite law_78.
  now rewrite next_and.
Qed.

Theorem (* 107 *) law_107 (p q : t) : □ p ⟹ (◇ q ⇒ ◇ (p ∧ q)).
Proof.
  apply and_impl_iff.
  now rewrite law_88.
Qed.

Theorem (* 108 *) law_108 (p q : t) : □ p ⟹ (□ q ⇒ □ (p ∧ q)).
Proof.
  apply and_impl_iff.
  now rewrite law_99.
Qed.

Theorem (* 109 *) law_109 (p q : t) : □ p ⟹ (◯ q ⇒ ◯ (p ∨ q)).
Proof.
  apply and_impl_iff.
  rewrite law_78.
  rewrite next_or.
  now rewrite and_proj, <- or_inj.
Qed.

Theorem (* 110 *) law_110 (p q : t) : □ p ⟹ (◇ q ⇒ ◇ (p ∨ q)).
Proof.
  apply and_impl_iff.
  rewrite law_88.
  rewrite law_53.
  rewrite evn_or.
  now rewrite and_proj, <- or_inj.
Qed.

Theorem (* 111 *) law_111 (p q : t) : □ p ⟹ (□ q ⇒ □ (p ∨ q)).
Proof.
  apply and_impl_iff.
  rewrite <- law_100.
  now rewrite and_proj, <- or_inj.
Qed.

Theorem (* 112 *) law_112 (p q : t) : □ p ⟹ (◯ q ⇒ ◯ (p ⇒ q)).
Proof.
  apply and_impl_iff.
  rewrite law_78.
  (* rewrite !impl_def. *)
  rewrite next_or.
  now rewrite and_comm, and_proj, or_comm, <- or_inj.
Qed.

Theorem (* 113 *) law_113 (p q : t) : □ p ⟹ (◇ q ⇒ ◇ (p ⇒ q)).
Proof.
  apply and_impl_iff.
  rewrite law_88.
  rewrite law_53.
  (* rewrite !impl_def. *)
  rewrite evn_or.
  now rewrite and_comm, and_proj, or_comm, <- or_inj.
Qed.

Theorem (* 114 *) law_114 (p q : t) : □ p ⟹ (□ q ⇒ □ (p ⇒ q)).
Proof.
  apply and_impl_iff.
  (* rewrite !impl_def. *)
  rewrite <- law_100.
  now rewrite and_comm, and_proj, or_comm, <- or_inj.
Qed.

Theorem (* 115 *) law_115 (p q : t) : □ p ⟹ (◯ q ⇒ ◯ (p ≡ q)).
Proof.
  apply and_impl_iff.
  rewrite law_78.
  rewrite !next_eqv.
  boolean.
  rewrite <- !or_inj_r.
  now boolean.
Qed.

Theorem (* 116 *) law_116 (p q : t) : □ p ⟹ (◇ q ⇒ ◇ (p ≡ q)).
Proof.
  apply and_impl_iff.
  rewrite law_88.
  boolean.
  rewrite <- !or_inj_r.
  now rewrite (and_comm q).
Qed.

Theorem (* 117 *) law_117 (p q : t) : □ p ⟹ (□ q ⇒ □ (p ≡ q)).
Proof.
  apply and_impl_iff.
  boolean.
  rewrite law_99.
  rewrite <- !or_inj_r.
  now boolean.
Qed.

Theorem (* 118 *) law_118 (p q : t) : □ (p ⇒ q) ⟹ (◯ p ⇒ ◯ q).
Proof.
  apply and_impl_iff.
  rewrite law_78.
  (* rewrite impl_def. *)
  rewrite !next_or.
  rewrite and_comm.
  rewrite and_or.
  rewrite next_not.
  now boolean.
Qed.

Theorem (* 119 *) law_119 (p q : t) : □ (p ⇒ q) ⟹ (◇ p ⇒ ◇ q).
Proof.
  apply and_impl_iff.
  rewrite law_88.
  boolean.
  rewrite law_53.
  now boolean.
Qed.

Theorem (* 120 *) law_120 (p q : t) : □ (p ⇒ q) ⟹ (□ p ⇒ □ q).
Proof.
  apply and_impl_iff.
  rewrite <- law_99.
  boolean.
  rewrite law_99.
  now boolean.
Qed.

Theorem (* 121 *) law_121 (p q r s : t) : □ ((p ⇒ q) ∧ (q ⇒ ◯ r) ∧ (r ⇒ s)) ⟹ (p ⇒ ◯ s).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite law_76.
  rewrite <- and_assoc.
  rewrite impl_trans.
  rewrite law_118.
  now rewrite impl_trans.
Qed.

Theorem (* 122 *) law_122 (p q r s : t) : □ ((p ⇒ q) ∧ (q ⇒ ◇ r) ∧ (r ⇒ s)) ⟹ (p ⇒ ◇ s).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite law_76.
  rewrite <- and_assoc.
  rewrite impl_trans.
  rewrite law_119.
  now rewrite impl_trans.
Qed.

Theorem (* 123 *) law_123 (p q r s : t) : □ ((p ⇒ q) ∧ (q ⇒ □ r) ∧ (r ⇒ s)) ⟹ (p ⇒ □ s).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite law_76.
  rewrite <- and_assoc.
  rewrite impl_trans.
  rewrite law_120.
  now rewrite impl_trans.
Qed.

Theorem (* 124 *) law_124 (p q r : t) : □ ((p ⇒ ◇ q) ∧ (q ⇒ ◇ r)) ⟹ (p ⇒ ◇ r).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite law_119.
  rewrite impl_trans.
  now rewrite law_50.
Qed.

Theorem (* 125 *) law_125 (p q r : t) : □ ((p ⇒ □ q) ∧ (q ⇒ □ r)) ⟹ (p ⇒ □ r).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite law_120.
  rewrite impl_trans.
  now rewrite law_72.
Qed.

Theorem (* 126 *) law_126 (p q r s : t) : □ ((p ⇒ q U r) ∧ (r ⇒ q U s)) ⟹ (p ⇒ q U s).
Proof.
  rewrite !law_99.
  rewrite law_76.
  rewrite (law_85 _ _ q).
  rewrite impl_trans.
  now rewrite until_left_absorb.
Qed.

Theorem (* 127 *) law_127 (p q r s : t) : □ ((p ⇒ r) ∧ (q ⇒ s)) ⟹ (p U q ⇒ r U s).
Proof.
  rewrite !law_99.
  rewrite (law_86 _ _ q).
  rewrite (law_85 _ _ r).
  now rewrite impl_trans.
Qed.

Theorem (* 128 *) law_128 (p q : t) : □ (p ∨ ◯ q ⇒ q) ⟹ (◇ p ⇒ q).
Proof.
  rewrite or_impl.
  rewrite law_99.
  rewrite evn_induction.
  rewrite law_119.
  now apply impl_trans.
Qed.

Theorem (* 129 *) law_129 (p q : t) : □ (p ⇒ q ∧ ◯ p) ⟹ (p ⇒ □ q).
Proof.
  pose proof (always_until_and_ind p q ⊥).
  rewrite until_right_bottom in H.
  rewrite !or_false in H.
  now rewrite and_comm.
Qed.

Theorem (* 130 *) law_130 (p q r : t) : □ (p ⇒ ¬q ∧ ◯ p) ⟹ (p ⇒ ¬(r U q)).
Proof.
  rewrite law_129.
  rewrite (law_81 (¬q) r).
  now rewrite not_not.
Qed.

Theorem (* 131 *) law_131 (p q r s : t) : □ ((p ⇒ ◇ (q ∨ r)) ∧ (q ⇒ ◇ s) ∧ (r ⇒ ◇ s)) ⟹ (p ⇒ ◇ s).
Proof.
  pose proof (law_124 p (q ∨ r) s).
  rewrite !law_99 in *.
  apply (proj1 (and_impl_iff _ _ _)) in H.
  apply (proj2 (and_impl_iff _ _ _)).
  rewrite H; clear H.
  (* rewrite !impl_def. *)
  apply or_respects_implies; [|reflexivity].
  rewrite <- law_99.
  rewrite !(or_comm _ (◇ s)).
  rewrite <- or_and.
  apply not_respects_implies; unfold Basics.flip.
  apply always_respects_implies.
  apply or_respects_implies; [reflexivity|].
  rewrite and_def.
  now boolean.
Qed.

Theorem (* 132 *) law_132 (p q : t) : □ (□ p ⇒ q) ⟹ (□ p ⇒ □ q).
Proof.
  apply and_impl_iff.
  rewrite <- (law_72 p) at 2.
  rewrite <- law_99.
  boolean.
  rewrite law_99.
  now boolean.
Qed.

Theorem (* 133 *) law_133 (p q : t) : □ (p ⇒ ◇ q) ⟹ (◇ p ⇒ ◇ q).
Proof.
  apply and_impl_iff.
  rewrite law_88.
  boolean.
  rewrite law_53.
  rewrite law_50.
  now boolean.
Qed.

Theorem (* 134 *) law_134 (p q : t) : □ (p ⇒ ◯ q) ⟹ (p ⇒ ◇ q).
Proof.
  apply and_impl_iff.
  rewrite (evn_weaken p) at 2.
  rewrite law_88.
  boolean.
  rewrite law_53.
  rewrite and_comm, and_proj.
  rewrite (law_45 q).
  rewrite or_comm, <- or_inj.
  now rewrite law_51.
Qed.

Theorem (* 135 *) law_135 (p : t) : □ (p ⇒ ◯ ¬p) ⟹ (p ⇒ ¬□ p).
Proof.
  apply and_impl_iff.
  rewrite and_proj.
  rewrite next_not.
  (* rewrite !impl_def. *)
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

Theorem (* 136 *) law_136 (p : t) : (⊤ ⟹ p) <-> (⊤ ⟹ □ p).
Proof.
  split; intros.
  - rewrite H.
    boolean.
    rewrite <- H at 2.
    rewrite law_64.
    now boolean.
  - rewrite H.
    now apply law_76.
Qed.

Corollary law_136b (p q : t) : (p ⟹ q) <-> (⊤ ⟹ □ (p ⇒ q)).
Proof.
  split; intros.
  - apply (proj1 (law_136 _)).
    apply and_impl_iff.
    now boolean.
  - apply law_136 in H.
    apply and_impl_iff in H.
    now rewrite true_and in H.
Qed.

Theorem until_metatheorem (p q r s : t) : (p ⟹ q) -> (r ⟹ s) -> (p U r ⟹ q U s).
Proof.
  intros.
  now apply until_respects_implies.
Qed.

Theorem (* 137 *) next_metatheorem (p q : t) : (p ⟹ q) -> (◯ p ⟹ ◯ q).
Proof.
  now apply next_respects_implies.
Qed.

Theorem (* 138 *) eventually_metatheorem (p q : t) : (p ⟹ q) -> (◇ p ⟹ ◇ q).
Proof.
  now apply eventually_respects_implies.
Qed.

Theorem (* 139 *) always_metatheorem (p q : t) : (p ⟹ q) -> (□ p ⟹ □ q).
Proof.
  now apply always_respects_implies.
Qed.

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
(148) U frame law of ◯ : □ p ⇒ (◯ q ⇒ ◯ (p U q))
(149) U frame law of ◇ : □ p ⇒ (◇ q ⇒ ◇ (p U q))
(150) U frame law of □ : □ p ⇒ (□ q ⇒ □ (p U q))
(151) Absorption of ◇ into □ ◇ : ◇ □ ◇ p ≡ □ ◇ p
(152) Absorption of □ into ◇ □ : □ ◇ □ p ≡ ◇ □ p
(153) Absorption of □ ◇ : □ ◇ □ ◇ p ≡ □ ◇ p
(154) Absorption of ◇ □ : ◇ □ ◇ □ p ≡ ◇ □ p
(155) Absorption of ◯ into □ ◇ : ◯ □ ◇ p ≡ □ ◇ p
(156) Absorption of ◯ into ◇ □ : ◯ ◇ □ p ≡ ◇ □ p
(157) Monotonicity of □ ◇ : □ (p ⇒ q) ⇒ (□ ◇ p ⇒ □ ◇ q)
(158) Monotonicity of ◇ □ : □ (p ⇒ q) ⇒ (◇ □ p ⇒ ◇ □ q)
(159) Distributivity of □ ◇ over ∧ : □ ◇ (p ∧ q) ⇒ □ ◇ p ∧ □ ◇ q
(160) Distributivity of ◇ □ over ∨ : ◇ □ p ∨ ◇ □ q ⇒ ◇ □ (p ∨ q)
(161) Distributivity of □ ◇ over ∨ : □ ◇ (p ∨ q) ≡ □ ◇ p ∨ □ ◇ q
(162) Distributivity of ◇ □ over ∧ : ◇ □ (p ∧ q) ≡ ◇ □ p ∧ ◇ □ q
(163) Eventual latching : ◇ □ (p ⇒ □ q) ≡ ◇ □ ¬p ∨ ◇ □ q
(164) □ (□ ◇ p ⇒ ◇ q) ≡ ◇ □ ¬p ∨ □ ◇ q
(165) □ ((p ∨ □ q) ∧ (□ p ∨ q)) ≡ □ p ∨ □ q
(166) ◇ □ p ∧ □ ◇ q ⇒ □ ◇ (p ∧ q)
(167) □ ((□ p ⇒ ◇ q) ∧ (q ⇒ ◯ r)) ⇒ (□ p ⇒ ◯ □ ◇ r)
(168) Progress proof rule : □ p ∧ □ (□ p ⇒ ◇ q) ⇒ ◇ q
*)

Theorem (* 140 *) law_140 (*U □ implication*) (p q : t) : p U □ q ⟹ □ (p U q).
Proof.
  assert (A : □ (p U □ q ⇒ p U q) ≈ ⊤).
    apply true_impl.
    rewrite <- (law_85 (□ q) q p).
    pose proof (law_76 q).
    apply impl_implies in H.
    rewrite <- H.
    now rewrite !law_64.
  assert (B : □ (p U □ q ⇒ ◯ (p U □ q)) ≈ ⊤).
    rewrite next_until.
    rewrite <- (until_absorb_u_or (◯ p)).
    rewrite (or_comm _ (◯ □ q)).
    rewrite <- next_until.
    apply true_impl.
    pose proof (and_proj (◯ □ q ∨ ◯ (p U □ q)) (q ∨ ◯ (p U □ q))).
    rewrite <- H.
    rewrite (and_comm _ (q ∨ ◯ (p U □ q))).
    rewrite <- or_and_r.
    rewrite <- law_66.
    pose proof (and_proj (□ q ∨ ◯ (p U □ q)) (□ q ∨ p)).
    rewrite <- H0.
    rewrite and_comm.
    rewrite <- or_and.
    rewrite <- until_expansion.
    boolean.
    now rewrite law_64.
  pose proof (law_129 (p U □ q) (p U q)).
  apply impl_implies.
  rewrite <- H.
  rewrite impl_and.
  rewrite law_99.
  rewrite A.
  rewrite B.
  now boolean.
Qed.

Theorem (* 141 *) law_141 (*Absorption of U into □*) (p : t) : p U □ p ≈ □ p.
Proof.
  split.
  - rewrite law_140.
    now rewrite until_idem.
  - now apply until_insertion.
Qed.

Theorem (* 142 *) law_142 (*Right ∧ U strengthening*) (p q r : t) : p U (q ∧ r) ⟹ p U (q U r).
Proof.
  pose proof (law_85 (q ∧ r) (q U r) p).
  apply impl_implies.
  rewrite <- H.
  rewrite <- until_30.
  boolean.
  now apply law_64.
Qed.

Theorem (* 143 *) law_143 (*Left ∧ U strengthening*) (p q r : t) : (p ∧ q) U r ⟹ (p U q) U r.
Proof.
  pose proof (law_86 (p ∧ q) (p U q)).
  apply impl_implies.
  rewrite <- H.
  rewrite <- until_30.
  boolean.
  now apply law_64.
Qed.

Theorem (* 144 *) law_144 (*Left ∧ U ordering*) (p q r : t) : (p ∧ q) U r ⟹ p U (q U r).
Proof.
  apply impl_implies.
  rewrite <- law_127.
  rewrite <- (proj1 (impl_implies _ _) (and_proj p q)).
  rewrite <- until_insertion.
  boolean.
  now apply law_64.
Qed.

Theorem (* 145 *) law_145 (*◇ □ implication*) (p : t) : ◇ □ p ⟹ □ ◇ p.
Proof.
  rewrite evn_def.
  rewrite law_140.
  now rewrite <- evn_def.
Qed.

Theorem (* 146 *) law_146 (*□ ◇ excluded middle*) (p : t) : □ ◇ p ∨ □ ◇ ¬p ≈ ⊤.
Proof.
  rewrite <- law_62.
  apply true_impl.
  rewrite <- law_145.
  now boolean.
Qed.

Theorem (* 147 *) law_147 (*◇ □ contradiction*) (p : t) : ◇ □ p ∧ ◇ □ ¬p ≈ ⊥.
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

Theorem (* 148 *) law_148 (*U frame law of ◯*) (p q : t) : □ p ⟹ (◯ q ⇒ ◯ (p U q)).
Proof.
  rewrite <- next_impl.
  rewrite <- until_insertion.
  boolean.
  rewrite next_true.
  now apply impl_true.
Qed.

Theorem (* 149 *) law_149 (*U frame law of ◇*) (p q : t) : □ p ⟹ (◇ q ⇒ ◇ (p U q)).
Proof.
  apply and_impl_iff.
  rewrite law_84.
  now apply evn_weaken.
Qed.

Theorem (* 150 *) law_150 (*U frame law of □*) (p q : t) : □ p ⟹ (□ q ⇒ □ (p U q)).
Proof.
  apply and_impl_iff.
  rewrite and_comm.
  rewrite and_proj.
  now rewrite <- until_insertion.
Qed.

Theorem (* 151 *) law_151 (*Absorption of ◇ into □ ◇*) (p : t) : ◇ □ ◇ p ≈ □ ◇ p.
Proof.
  split.
  - rewrite law_145.
    now rewrite law_50.
  - now rewrite evn_weaken at 1.
Qed.

Theorem (* 152 *) law_152 (*Absorption of □ into ◇ □*) (p : t) : □ ◇ □ p ≈ ◇ □ p.
Proof.
  rewrite <- (not_not p) at 1.
  rewrite <- law_63.
  rewrite <- law_61.
  rewrite law_151.
  rewrite <- law_62.
  now boolean.
Qed.

Theorem (* 153 *) law_153 (*Absorption of □ ◇*) (p : t) : □ ◇ □ ◇ p ≈ □ ◇ p.
Proof.
  rewrite law_152.
  now rewrite law_151.
Qed.

Theorem (* 154 *) law_154 (*Absorption of ◇ □*) (p : t) : ◇ □ ◇ □ p ≈ ◇ □ p.
Proof.
  rewrite law_151.
  now rewrite law_152.
Qed.

Theorem (* 155 *) law_155 (*Absorption of ◯ into □ ◇*) (p : t) : ◯ □ ◇ p ≈ □ ◇ p.
Proof.
  split.
  - rewrite (law_47 (□ ◇ p)).
    now rewrite law_151.
  - now apply law_79.
Qed.

Theorem (* 156 *) law_156 (*Absorption of ◯ into ◇ □*) (p : t) : ◯ ◇ □ p ≈ ◇ □ p.
Proof.
  split.
  - rewrite law_47.
    now rewrite law_50.
  - rewrite <- (law_78 (◇ □ p)) at 1.
    now rewrite law_152.
Qed.

Theorem (* 157 *) law_157 (*Monotonicity of □ ◇*) (p q : t) : □ (p ⇒ q) ⟹ (□ ◇ p ⇒ □ ◇ q).
Proof.
  transitivity (□ (◇ p ⇒ ◇ q)).
    rewrite <- law_72.
    apply always_metatheorem.
    now rewrite law_119.
  now rewrite law_120.
Qed.

Theorem (* 158 *) law_158 (*Monotonicity of ◇ □*) (p q : t) : □ (p ⇒ q) ⟹ (◇ □ p ⇒ ◇ □ q).
Proof.
  transitivity (□ (□ p ⇒ □ q)).
    rewrite <- law_72.
    apply always_metatheorem.
    now rewrite law_120.
  now rewrite law_119.
Qed.

Theorem (* 159 *) law_159 (*Distributivity of □ ◇ over ∧*) (p q : t) : □ ◇ (p ∧ q) ⟹ □ ◇ p ∧ □ ◇ q.
Proof.
  rewrite law_53.
  now rewrite law_99.
Qed.

Theorem (* 160 *) law_160 (*Distributivity of ◇ □ over ∨*) (p q : t) : ◇ □ p ∨ ◇ □ q ⟹ ◇ □ (p ∨ q).
Proof.
  rewrite <- evn_or.
  now rewrite law_100.
Qed.

Theorem (* 161 *) law_161 (*Distributivity of □ ◇ over ∨*) (p q : t) : □ ◇ (p ∨ q) ≈ □ ◇ p ∨ □ ◇ q.
Proof.
Proof.
  split.
  - assert (A : ◇ (◇ (p ∨ q) ∧ □ ¬p) ⟹ ◇ q).
      rewrite <- (and_proj (◇ q) (◇ ¬p)).
      rewrite (and_comm (◇ q)).
      rewrite <- law_53.
      rewrite <- (law_50 (¬ p ∧ q)).
      rewrite and_comm.
      apply eventually_metatheorem.
      rewrite <- (and_absorb (¬p) q) at 2.
      rewrite law_88.
      rewrite and_or.
      now boolean.
    pose proof (law_88 (◇ (p ∨ q)) (□ ¬p)).
    rewrite A in H.
    apply always_metatheorem in H.
    rewrite law_99 in H.
    rewrite law_72 in H.
    rewrite law_152 in H.
    apply and_impl_iff in H.
    rewrite <- law_63 in H.
    (* rewrite impl_def in H. *)
    rewrite not_not in H.
    now apply H.
  - rewrite evn_or.
    now rewrite law_100.
Qed.

Theorem (* 162 *) law_162 (*Distributivity of ◇ □ over ∧*) (p q : t) : ◇ □ (p ∧ q) ≈ ◇ □ p ∧ ◇ □ q.
Proof.
  rewrite <- (not_not p) at 1.
  rewrite <- (not_not q) at 1.
  rewrite <- not_or.
  rewrite <- law_63.
  rewrite law_161.
  rewrite <- !law_62.
  rewrite not_or.
  now boolean.
Qed.

Theorem (* 163 *) law_163 (*Eventual latching*) (p q : t) : ◇ □ (p ⇒ □ q) ≈ ◇ □ ¬p ∨ ◇ □ q.
Proof.
  assert (A : ◇ □ (p ⇒ □ q) ⟹ ◇ (□ ◇ p ⇒ ◇ □ q)). {
    rewrite <- (evn_weaken (□ ◇ p ⇒ ◇ □ q)).
    rewrite <- (law_50 (□ q)).
    rewrite <- law_104.
    rewrite <- (law_76 (◇ (◇ p ⇒ ◇ □ q))).
    rewrite <- law_152.
    apply impl_implies.
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
    (* rewrite impl_def. *)
    now rewrite law_63.
  - rewrite <- (law_72 q) at 1.
    (* rewrite impl_def. *)
    now rewrite law_160.
Qed.

Theorem (* 164 *) law_164 (p q : t) : □ (□ ◇ p ⇒ ◇ q) ≈ ◇ □ ¬p ∨ □ ◇ q.
Proof.
  split.
  - rewrite law_120.
    rewrite law_72.
    (* rewrite impl_def. *)
    now rewrite law_63.
  - (* rewrite impl_def. *)
    rewrite <- law_100.
    rewrite law_63.
    now rewrite <- law_152 at 1.
Qed.

Theorem (* 165 *) law_165 (p q : t) : □ ((p ∨ □ q) ∧ (□ p ∨ q)) ≈ □ p ∨ □ q.
Proof.
  set (r := (p ∨ □ q) ∧ (□ p ∨ q)).

  assert (A : r ≈ □ p ∨ □ q ∨ (p ∧ q)).
    unfold r.
    rewrite or_and_or.
    rewrite 2 law_68.
    rewrite (or_comm _ (□ q)).
    rewrite (and_comm _ (□ q)).
    rewrite or_absorb.
    rewrite (or_comm _ (□ q)).
    reflexivity.

  assert (B : □ r ∧ ¬□ p ∧ ¬□ q ⟹ ◯ (□ r ∧ ¬□ p ∧ ¬□ q)).
    rewrite law_66 at 1.
    rewrite (and_comm r).
    rewrite A at 2.
    rewrite and_assoc.
    rewrite <- (and_assoc _ (¬ □ p)).
    rewrite (and_comm _ (¬ □ p)).
    rewrite <- (not_not (□ p)) at 2.
    (* rewrite <- impl_def. *)
    rewrite and_apply.
    rewrite and_assoc.
    rewrite (and_comm _ (¬ □ q)).
    rewrite <- (not_not (□ q)) at 2.
    (* rewrite <- impl_def. *)
    rewrite and_apply.
    rewrite <- !and_assoc.
    rewrite and_assoc.
    rewrite (and_assoc (◯ □ r)).
    rewrite and_comm.
    rewrite <- !and_assoc.
    rewrite (and_comm _ (◯ □ r)).
    rewrite !and_assoc.
    rewrite (law_66 p) at 1.
    rewrite (law_66 q) at 1.
    rewrite 2 not_and.
    rewrite <- (and_assoc q).
    rewrite (and_comm q).
    rewrite !and_assoc.
    (* rewrite <- !impl_def. *)
    rewrite and_apply.
    rewrite <- (and_assoc p).
    rewrite and_apply.
    rewrite (and_comm p).
    rewrite (and_comm q).
    rewrite (and_proj _ p).
    rewrite (and_proj _ q).
    rewrite <- !next_not.
    rewrite <- !next_and.
    reflexivity.

  assert (C : □ r ∧ ¬□ p ∧ ¬□ q ⟹ □ (□ r ∧ ¬□ p ∧ ¬□ q)).
    apply impl_implies in B.
    apply always_respects_implies in B.
    rewrite always_induction in B.
    rewrite law_64 in B.
    apply impl_implies in B.
    exact B.

  assert (D : □ (□ r ∧ ¬□ p ∧ ¬□ q) ⟹ □ p ∧ □ q).
    rewrite <- law_99.
    apply impl_implies.
    rewrite <- law_120.
    apply (proj1 (law_136b _ _)).
    apply and_impl_iff.
    (* rewrite impl_def. *)
    rewrite not_and.
    rewrite !not_not.
    rewrite or_assoc.
    rewrite <- A.
    now apply law_76.

  assert (E : □ r ∧ ¬□ p ∧ ¬□ q ⟹ □ p ∧ □ q).
    rewrite C.
    now rewrite D.

  assert (F : □ p ∨ □ q ⟹ ◯ (□ p ∨ □ q)).
    rewrite (law_66 p) at 1.
    rewrite (law_66 q) at 1.
    rewrite (and_comm p).
    rewrite (and_comm q).
    rewrite (and_proj _ p).
    rewrite (and_proj _ q).
    now rewrite <- next_or.

  assert (G : □ (□ p ∨ □ q) ⟹ □ r).
    apply impl_implies.
    rewrite <- law_120.
    apply (proj1 (law_136b _ _)).
    rewrite A.
    rewrite <- or_assoc.
    now rewrite <- (or_inj _ (p ∧ q)).

  split.
  - apply impl_implies.
    apply contrapositive.
    rewrite not_true.
    (* rewrite impl_def. *)
    rewrite !not_or.
    rewrite not_not.
    rewrite <- (and_idem (□ r ∧ ¬ □ p ∧ ¬ □ q)).
    rewrite E at 2.
    rewrite !and_assoc.
    rewrite (and_comm _ (□ q)).
    rewrite <- (and_assoc (¬ □ q)).
    rewrite (and_comm _ (□ q)).
    now boolean.

  - rewrite <- G.
    apply impl_implies.
    rewrite <- always_induction.
    rewrite <- F.
    boolean.
    now rewrite law_64.
Qed.

Theorem (* 166 *) law_166 (p q : t) : ◇ □ p ∧ □ ◇ q ⟹ □ ◇ (p ∧ q).
Proof.
  apply and_impl_iff.
  rewrite <- (law_72 (◇ q)).
  rewrite <- (law_151 (p ∧ q)).
  rewrite <- law_104.
  apply eventually_metatheorem.
  apply and_impl_iff.
  rewrite <- law_72.
  rewrite <- law_99.
  now rewrite law_88.
Qed.

Theorem (* 167 *) law_167 (p q r : t) : □ ((□ p ⇒ ◇ q) ∧ (q ⇒ ◯ r)) ⟹ (□ p ⇒ ◯ □ ◇ r).
Proof.
  apply and_impl_iff.
  rewrite law_99.
  rewrite (evn_weaken (□ p)) at 2.
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

Theorem (* 168 *) law_168 (*Progress proof rule*) (p q : t) : ◇ □ p ∧ □ (□ p ⇒ ◇ q) ⟹ ◇ q.
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
(188) Right distributivity of W over ⇒ : (p ⇒ q) W r ⇒ (p W r ⇒ q W r)
(189) Disjunction rule of W : p W q ≡ (p ∨ q) W q
(190) Disjunction rule of U : p U q ≡ (p ∨ q) U q
(191) Rule of W : ¬q W q
(192) Rule of U : ¬q U q ≡ ◇ q
(193) (p ⇒ q) W p
(194) ◇ p ⇒ (p ⇒ q) U p
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
(208) □ (¬q ⇒ p) ⇒ p W q
(209) W insertion: q ⇒ p W q
(210) W frame law of ◯ : □ p ⇒ (◯ q ⇒ ◯ (p W q))
(211) W frame law of ◇ : □ p ⇒ (◇ q ⇒ ◇ (p W q))
(212) W frame law of □ : □ p ⇒ (□ q ⇒ □ (p W q))
(213) W induction: □ (p ⇒ (◯ p ∧ q) ∨ r) ⇒ (p ⇒ q W r)
(214) W induction: □ (p ⇒ ◯ (p ∨ q)) ⇒ (p ⇒ p W q)
(215) W induction: □ (p ⇒ ◯ p) ⇒ (p ⇒ p W q)
(216) W induction: □ (p ⇒ q ∧ ◯ p) ⇒ (p ⇒ p W q)
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
(238) Left monotonicity of W : □ (p ⇒ q) ⇒ (p W r ⇒ q W r)
(239) Right monotonicity of W : □ (p ⇒ q) ⇒ (r W p ⇒ r W q)
(240) W strengthening rule : □ ((p ⇒ r) ∧ (q ⇒ s)) ⇒ (p W q ⇒ r W s)
(241) W catenation rule: □ ((p ⇒ q W r) ∧ (r ⇒ q W s)) ⇒ (p ⇒ q W s)
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
(254) Lemmon formula: □ (□ p ⇒ q) ∨ □ (□ q ⇒ p)
*)

Theorem (* 170 *) not_wait (p q : t) : ¬(p W q) ≈ ¬q U (¬p ∧ ¬q).
Proof.
  rewrite wait_def.
  rewrite <- not_until.
  rewrite not_or.
  rewrite always_def.
  rewrite evn_def.
  now boolean.
Qed.

Theorem (* 171 *) law_171 (* U in terms of W *) (p q : t) : p U q ≈ p W q ∧ ◇ q.
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

Theorem (* 172 *) law_172 (p q : t) : p W q ≈ □ (p ∧ ¬q) ∨ p U q.
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

Theorem (* 173 *) law_173 (*Distributivity of ¬ over U *) (p q : t) : ¬(p U q) ≈ ¬q W (¬p ∧ ¬q).
Proof.
  rewrite law_171.
  rewrite not_and.
  rewrite not_wait.
  rewrite wait_def.
  rewrite or_comm.
  apply or_respects_equivalent; [|reflexivity].
  now apply law_61.
Qed.

Theorem (* 174 *) law_174 (*U implication*) (p q : t) : p U q ⟹ p W q.
Proof.
  rewrite law_171.
  now boolean.
Qed.

Theorem (* 175 *) law_175 (*Distributivity of ∧ over W *) (p q r : t) : □ p ∧ q W r ⟹ (p ∧ q) W (p ∧ r).
Proof.
  rewrite wait_def.
  rewrite and_or.
  rewrite law_83.
  rewrite <- law_99.
  now rewrite <- wait_def.
Qed.

Theorem (* 176 *) law_176 (*W ◇ equivalence*) (p q : t) : p W ◇ q ≈ □ p ∨ ◇ q.
Proof.
  rewrite wait_def.
  now rewrite until_absorb_evn.
Qed.

Theorem (* 177 *) law_177 (*W □ implication*) (p q : t) : p W □ q ⟹ □ (p W q).
Proof.
  rewrite (wait_def _ q).
  rewrite <- law_100.
  rewrite law_72.
  rewrite <- law_140.
  now rewrite <- wait_def.
Qed.

Theorem (* 178 *) law_178 (*Absorption of W into □ *) (p : t) : p W □ p ≈ □ p.
Proof.
  rewrite wait_def.
  rewrite law_141.
  now boolean.
Qed.

Theorem (* 179 *) law_179 (*Perpetuity*) (p q : t) : □ p ⟹ p W q.
Proof.
  rewrite (or_inj _ (p U q)).
  now rewrite <- wait_def.
Qed.

Theorem (* 180 *) law_180 (*Distributivity of ◯ over W *) (p q : t) : ◯ (p W q) ≈ ◯ p W ◯ q.
Proof.
  rewrite wait_def.
  rewrite next_or.
  rewrite law_73.
  rewrite next_until.
  now rewrite <- wait_def.
Qed.

Theorem (* 181 *) law_181 (*Expansion of W *) (p q : t) : p W q ≈ q ∨ (p ∧ ◯ (p W q)).
Proof.
  rewrite wait_def at 2.
  rewrite next_or.
  rewrite and_or.
  rewrite <- law_66.
  rewrite <- or_assoc.
  rewrite (or_comm q).
  rewrite or_assoc.
  rewrite <- until_expansion.
  now rewrite <- wait_def.
Qed.

Theorem (* 182 *) law_182 (*W excluded middle*) (p q : t) : p W q ∨ p W ¬q ≈ ⊤.
Proof.
  rewrite law_181.
  rewrite (law_181 _ (¬q)).
  rewrite (or_comm q).
  rewrite or_assoc.
  rewrite !or_and.
  rewrite <- (or_assoc q).
  boolean.
  rewrite <- (or_assoc q).
  now boolean.
Qed.

Theorem (* 183 *) law_183 (*Left zero of W *) (q : t) : ⊤ W q ≈ ⊤.
Proof.
  rewrite wait_def.
  rewrite law_64.
  now boolean.
Qed.

Theorem (* 184 *) law_184 (*Left distributivity of W over ∨ *) (p q r : t) : p W (q ∨ r) ≈ p W q ∨ p W r.
Proof.
  rewrite wait_def.
  rewrite until_left_or.
  rewrite <- (or_idem (□ p)).
  rewrite or_assoc.
  rewrite <- (or_assoc (□ p) (until _ _)).
  rewrite or_comm.
  rewrite !or_assoc.
  rewrite (or_comm (until _ _) (□ p)).
  rewrite <- wait_def.
  rewrite <- or_assoc.
  now rewrite <- wait_def.
Qed.

Theorem (* 185 *) law_185 (*Right distributivity of W over ∨ *) (p q r : t) : p W r ∨ q W r ⟹ (p ∨ q) W r.
Proof.
  rewrite 2 wait_def.
  rewrite <- or_assoc.
  rewrite (or_comm _ (□ q)).
  rewrite <- or_assoc.
  rewrite (or_comm (□ q)).
  rewrite law_100.
  rewrite !or_assoc.
  rewrite until_right_or.
  now rewrite <- wait_def.
Qed.

Theorem (* 186 *) law_186 (*Left distributivity of W over ∧ *) (p q r : t) : p W (q ∧ r) ⟹ p W q ∧ p W r.
Proof.
  rewrite wait_def.
  rewrite until_left_and.
  rewrite or_and.
  now rewrite <- !wait_def.
Qed.

Theorem (* 187 *) law_187 (*Right distributivity of W over ∧ *) (p q r : t) : (p ∧ q) W r ≈ p W r ∧ q W r.
Proof.
  rewrite <- not_not.
  rewrite not_wait.
  rewrite (and_comm _ (¬r)).
  rewrite not_and.
  rewrite and_or.
  rewrite !(and_comm (¬r)).
  rewrite until_left_or.
  rewrite <- !not_wait.
  rewrite <- not_and.
  now boolean.
Qed.

Theorem (* 188 *) law_188 (*Right distributivity of W over ⟹ *) (p q r : t) : (p ⇒ q) W r ⟹ (p W r ⇒ q W r).
Proof.
  apply and_impl_iff.
  rewrite <- law_187.
  rewrite impl_apply.
  rewrite law_187.
  now boolean.
Qed.

Theorem (* 189 *) law_189 (*Disjunction rule of W *) (p q : t) : p W q ≈ (p ∨ q) W q.
Proof.
  rewrite <- not_not.
  rewrite not_wait.
  rewrite law_173.
  rewrite !not_and.
  boolean.
  rewrite or_comm.
  now rewrite and_absorb.
Qed.

Theorem (* 190 *) law_190 (*Disjunction rule of U *) (p q : t) : p U q ≈ (p ∨ q) U q.
Proof.
  rewrite <- not_not.
  rewrite law_173.
  rewrite not_wait.
  rewrite !not_and.
  boolean.
  rewrite or_comm.
  now rewrite and_absorb.
Qed.

Theorem (* 191 *) law_191 (*Rule of W *) (q : t) : ¬q W q ≈ ⊤.
Proof.
  rewrite law_189.
  boolean.
  now rewrite law_183.
Qed.

Theorem (* 192 *) law_192 (*Rule of U *) (q : t) : ¬q U q ≈ ◇ q.
Proof.
  rewrite law_190.
  boolean.
  now rewrite evn_def.
Qed.

Theorem (* 193 *) law_193 (p q : t) : (p ⇒ q) W p ≈ ⊤.
Proof.
  apply true_impl.
  (* rewrite impl_def. *)
  rewrite <- law_185.
  rewrite law_191.
  now boolean.
Qed.

Theorem (* 194 *) law_194 (p q : t) : ◇ p ⟹ (p ⇒ q) U p.
Proof.
  (* rewrite impl_def. *)
  rewrite <- until_right_or.
  rewrite <- or_inj.
  now rewrite <- law_192.
Qed.

Theorem (* 195 *) law_195 (*Conjunction rule of W *) (p q : t) : p W q ≈ (p ∧ ¬q) W q.
Proof.
  rewrite law_187.
  rewrite law_191.
  now boolean.
Qed.

Theorem (* 196 *) law_196 (*Conjunction rule of U *) (p q : t) : p U q ≈ (p ∧ ¬q) U q.
Proof.
  rewrite (law_171 (and _ _)).
  rewrite <- law_195.
  now rewrite <- law_171.
Qed.

Theorem (* 197 *) law_197 (*Distributivity of ¬ over W *) (p q : t) : ¬(p W q) ≈ (p ∧ ¬q) U (¬p ∧ ¬q).
Proof.
  rewrite not_wait.
  rewrite law_196.
  rewrite not_and.
  boolean.
  rewrite and_or.
  boolean.
  now rewrite and_comm.
Qed.

Theorem (* 198 *) law_198 (*Distributivity of ¬ over U *) (p q : t) : ¬(p U q) ≈ (p ∧ ¬q) W (¬p ∧ ¬q).
Proof.
  rewrite law_173.
  rewrite law_195.
  rewrite not_and.
  boolean.
  rewrite and_or.
  boolean.
  now rewrite and_comm.
Qed.

Theorem (* 199 *) law_199 (*Dual of U *) (p q : t) : ¬(¬p U ¬q) ≈ q W (p ∧ q).
Proof.
  rewrite law_173.
  now boolean.
Qed.

Theorem (* 200 *) law_200 (*Dual of U *) (p q : t) : ¬(¬p U ¬q) ≈ (¬p ∧ q) W (p ∧ q).
Proof.
  rewrite law_198.
  now boolean.
Qed.

Theorem (* 201 *) law_201 (*Dual of W *) (p q : t) : ¬(¬p W ¬q) ≈ q U (p ∧ q).
Proof.
  rewrite not_wait.
  now boolean.
Qed.

Theorem (* 202 *) law_202 (*Dual of W *) (p q : t) : ¬(¬p W ¬q) ≈ (¬p ∧ q) U (p ∧ q).
Proof.
  rewrite law_197.
  now boolean.
Qed.

Theorem (* 203 *) law_203 (*Idempotency of W *) (p : t) : p W p ≈ p.
Proof.
  rewrite wait_def.
  rewrite until_idem.
  now rewrite law_69.
Qed.

Theorem (* 204 *) law_204 (*Right zero of W *) (p : t) : p W ⊤ ≈ ⊤.
Proof.
  rewrite wait_def.
  rewrite until_true.
  now boolean.
Qed.

Theorem (* 205 *) law_205 (*Left identity of W *) (q : t) : ⊥ W q ≈ q.
Proof.
  rewrite wait_def.
  rewrite false_until.
  rewrite law_65.
  now boolean.
Qed.

Theorem (* 206 *) law_206 (p q : t) : p W q ⟹ p ∨ q.
Proof.
  rewrite law_181.
  rewrite or_and.
  rewrite or_comm.
  now boolean.
Qed.

Theorem (* 207 *) law_207 (p q : t) : □ (p ∨ q) ⟹ p W q.
Proof.
  rewrite law_179.
  now rewrite <- law_189.
Qed.

Theorem (* 208 *) law_208 (p q : t) : □ (¬q ⇒ p) ⟹ p W q.
Proof.
  (* rewrite impl_def. *)
  rewrite or_comm.
  rewrite not_not.
  now rewrite law_207.
Qed.

Theorem (* 209 *) law_209 (*W insertion*) (p q : t) : q ⟹ p W q.
Proof.
  rewrite law_181.
  now boolean.
Qed.

Theorem (* 210 *) law_210 (*W frame law of ◯ *) (p q : t) : □ p ⟹ (◯ q ⇒ ◯ (p W q)).
Proof.
  rewrite <- next_impl.
  rewrite <- law_209.
  boolean.
  rewrite next_true.
  now apply impl_true.
Qed.

Theorem (* 211 *) law_211 (*W frame law of ◇ *) (p q : t) : □ p ⟹ (◇ q ⇒ ◇ (p W q)).
Proof.
  apply and_impl_iff.
  rewrite law_84.
  rewrite law_174.
  now apply evn_weaken.
Qed.

Theorem (* 212 *) law_212 (*W frame law of □ *) (p q : t) : □ p ⟹ (□ q ⇒ □ (p W q)).
Proof.
  apply and_impl_iff.
  rewrite and_comm.
  rewrite and_proj.
  rewrite (law_209 p (□ q)).
  now rewrite <- law_177.
Qed.

Theorem (* 213 *) law_213 (*W induction*) (p q r : t) : □ (p ⇒ (◯ p ∧ q) ∨ r) ⟹ (p ⇒ q W r).
Proof.
  rewrite wait_def.
  now rewrite always_until_and_ind.
Qed.

Theorem (* 214 *) law_214 (*W induction*) (p q : t) : □ (p ⇒ ◯ (p ∨ q)) ⟹ (p ⇒ p W q).
Proof.
  rewrite always_until_or_ind.
  now rewrite <- wait_def.
Qed.

Theorem (* 215 *) law_215 (*W induction*) (p q : t) : □ (p ⇒ ◯ p) ⟹ (p ⇒ p W q).
Proof.
  rewrite always_induction.
  now rewrite <- law_179.
Qed.

Theorem (* 216 *) law_216 (*W induction*) (p q : t) : □ (p ⇒ q ∧ ◯ p) ⟹ (p ⇒ p W q).
Proof.
  rewrite impl_and.
  rewrite law_99.
  rewrite and_comm.
  rewrite and_proj.
  rewrite always_induction.
  now rewrite <- law_179.
Qed.

Theorem (* 217 *) law_217 (*Absorption*) (p q : t) : p ∨ p W q ≈ p ∨ q.
Proof.
  rewrite wait_def.
  rewrite <- or_assoc.
  rewrite (or_comm p).
  rewrite law_69.
  now rewrite until_absorb_or_u.
Qed.

Theorem (* 218 *) law_218 (*Absorption*) (p q : t) : p W q ∨ q ≈ p W q.
Proof.
  rewrite or_comm.
  apply or_eqv_impl.
  now apply law_209.
Qed.

Theorem (* 219 *) law_219 (*Absorption*) (p q : t) : p W q ∧ q ≈ q.
Proof.
  rewrite and_comm.
  apply and_eqv_impl.
  now apply law_209.
Qed.

Theorem (* 220 *) law_220 (*Absorption*) (p q : t) : p W q ∧ (p ∨ q) ≈ p W q.
Proof.
  apply and_eqv_impl.
  now apply law_206.
Qed.

Theorem (* 221 *) law_221 (*Absorption*) (p q : t) : p W q ∨ (p ∧ q) ≈ p W q.
Proof.
  rewrite law_181 at 1.
  rewrite (and_comm _ q).
  rewrite (or_comm q).
  rewrite or_assoc.
  rewrite or_absorb.
  rewrite (or_comm _ q).
  now rewrite <- law_181.
Qed.

Theorem (* 222 *) law_222 (*Left absorption of W *) (p q : t) : p W (p W q) ≈ p W q.
Proof.
  rewrite !wait_def.
  rewrite until_left_or.
  rewrite until_left_absorb.
  rewrite law_141.
  rewrite <- or_assoc.
  now boolean.
Qed.

Theorem (* 223 *) law_223 (*Right absorption of W *) (p q : t) : (p W q) W q ≈ p W q.
Proof.
  split.
  - rewrite law_206.
    now rewrite law_218.
  - rewrite (wait_def p) at 2.
    rewrite <- law_185.
    rewrite <- (law_174 (until _ _)).
    rewrite until_right_absorb.
    rewrite <- (law_179 (always _)).
    rewrite law_72.
    now rewrite <- wait_def.
Qed.

Theorem (* 224 *) law_224 (*□ to W law*) (p : t) : □ p ≈ p W ⊥.
Proof.
  rewrite wait_def.
  rewrite until_right_bottom.
  now boolean.
Qed.

Theorem (* 225 *) law_225 (*◇ to W law*) (p : t) : ◇ p ≈ ¬(¬p W ⊥).
Proof.
  rewrite <- law_224.
  now rewrite <- law_59.
Qed.

Theorem (* 226 *) law_226 (*W implication*) (p q : t) : p W q ⟹ □ p ∨ ◇ q.
Proof.
  rewrite wait_def.
  now rewrite law_42.
Qed.

Theorem (* 227 *) law_227 (*Absorption*) (p q : t) : p W (p U q) ≈ p W q.
Proof.
  rewrite wait_def.
  rewrite until_left_absorb.
  now rewrite <- wait_def.
Qed.

Theorem (* 228 *) law_228 (*Absorption*) (p q : t) : (p U q) W q ≈ p U q.
Proof.
  rewrite wait_def.
  rewrite until_right_absorb.
  now rewrite law_69.
Qed.

Theorem (* 229 *) law_229 (*Absorption*) (p q : t) : p U (p W q) ≈ p W q.
Proof.
  rewrite wait_def.
  rewrite until_left_or.
  rewrite until_left_absorb.
  now rewrite law_141.
Qed.

Theorem (* 230 *) law_230 (*Absorption*) (p q : t) : (p W q) U q ≈ p U q.
Proof.
  rewrite law_171.
  rewrite law_223.
  now rewrite law_171.
Qed.

Theorem (* 231 *) law_231 (*Absorption of W into ◇ *) (q : t) : ◇ q W q ≈ ◇ q.
Proof.
  rewrite evn_def.
  now rewrite law_228.
Qed.

Theorem (* 232 *) law_232 (*Absorption of W into □ *) (p q : t) : □ p ∧ p W q ≈ □ p.
Proof.
  rewrite wait_def.
  now rewrite and_absorb.
Qed.

Theorem (* 233 *) law_233 (*Absorption of □ into W *) (p q : t) : □ p ∨ p W q ≈ p W q.
Proof.
  rewrite wait_def.
  rewrite <- or_assoc.
  now boolean.
Qed.

Theorem (* 234 *) law_234 (p q : t) : p W q ∧ □ ¬q ⟹ □ p.
Proof.
  rewrite law_226.
  rewrite <- law_61.
  rewrite or_comm.
  rewrite and_comm.
  rewrite <- (not_not (◇ q)).
  rewrite not_not.
  (* rewrite <- impl_def. *)
  rewrite and_apply.
  now boolean.
Qed.

Theorem (* 235 *) law_235 (p q : t) : □ p ⟹ p U q ∨ □ ¬q.
Proof.
  rewrite <- law_84.
  rewrite <- law_61.
  rewrite or_comm.
  rewrite and_comm.
  rewrite <- (not_not (◇ q)) at 2.
  rewrite or_not_absorb.
  now boolean.
Qed.

Lemma (* NEW *) not_always_until (p q : t) : □ ¬p ∧ p U q ⟹ q.
Proof.
  rewrite always_def.
  rewrite not_not.
  rewrite evn_def.
  rewrite and_comm.
  rewrite and_impl_iff.
  (* rewrite impl_def. *)
  rewrite not_not.
  rewrite until_28.
  rewrite <- until_30.
  now boolean.
Qed.

Lemma (* NEW *) always_until_left (p q : t) : □ p U q ⟹ p U q ∨ □ ¬q.
Proof.
  rewrite <- or_inj.
  apply until_respects_implies; [|reflexivity].
  now apply law_76.
Qed.

Theorem (* 236 *) law_236 (p q : t) : ¬□ p ∧ p W q ⟹ ◇ q.
Proof.
  rewrite and_comm.
  apply and_impl_iff.
  rewrite law_226.
  now boolean.
Qed.

Theorem (* 237 *) law_237 (p q : t) : ◇ q ⟹ ¬□ p ∨ p U q.
Proof.
  (* rewrite <- impl_def. *)
  apply and_impl_iff.
  rewrite and_comm.
  now rewrite law_84.
Qed.

Theorem (* NEW *) law_237b (p q : t) : ◇ q ⟹ □ p ⇒ p U q.
Proof.
  apply and_impl_iff.
  rewrite and_comm.
  now rewrite law_84.
Qed.

Theorem (* 238 *) law_238 (*Left monotonicity of W *) (p q r : t) : □ (p ⇒ q) ⟹ (p W r ⇒ q W r).
Proof.
  apply and_impl_iff.
  rewrite law_175.
  rewrite and_comm.
  (* rewrite impl_def. *)
  rewrite and_not_absorb.
  rewrite law_186.
  rewrite (law_187 _ _ r).
  rewrite and_comm.
  rewrite and_proj.
  now boolean.
Qed.

Theorem (* 239 *) law_239 (*Right monotonicity of W *) (p q r : t) : □ (p ⇒ q) ⟹ (r W p ⇒ r W q).
Proof.
  rewrite !wait_def.
  rewrite !(or_comm (□ r)).
  rewrite <- or_monotonicity.
  now rewrite <- law_85.
Qed.

Theorem (* 240 *) law_240 (*W strengthening rule *) (p q r s : t) : □ ((p ⇒ r) ∧ (q ⇒ s)) ⟹ (p W q ⇒ r W s).
Proof.
  apply and_impl_iff.
  rewrite law_99.
  rewrite (law_239 q s p).
  rewrite and_assoc.
  rewrite (and_comm _ (wait _ _)).
  rewrite and_apply.
  rewrite (and_comm (wait _ _)).
  rewrite (and_proj _ (p W q)).
  rewrite (law_238 p r s).
  rewrite and_comm.
  rewrite and_apply.
  now boolean.
Qed.

Theorem (* 241 *) law_241 (*W catenation rule*) (p q r s : t) : □ ((p ⇒ q W r) ∧ (r ⇒ q W s)) ⟹ (p ⇒ q W s).
Proof.
  apply and_impl_iff.
  rewrite law_99.
  rewrite law_76.
  rewrite and_comm.
  rewrite <- and_assoc.
  rewrite and_apply.
  rewrite (law_239 r (q W s) q).
  rewrite and_assoc.
  rewrite and_apply.
  rewrite law_222.
  rewrite <- and_assoc.
  now boolean.
Qed.

Theorem (* 242 *) law_242 (*Left U W implication*) (p q r : t) : (p U q) W r ⟹ (p W q) W r.
Proof.
  now rewrite law_174.
Qed.

Theorem (* 243 *) law_243 (*Right W U implication*) (p q r : t) : p W (q U r) ⟹ p W (q W r).
Proof.
  now rewrite law_174.
Qed.

Theorem (* 244 *) law_244 (*Right U U implication*) (p q r : t) : p U (q U r) ⟹ p U (q W r).
Proof.
  now rewrite <- law_174.
Qed.

Theorem (* 245 *) law_245 (*Left U U implication*) (p q r : t) : (p U q) U r ⟹ (p W q) U r.
Proof.
  now rewrite <- law_174.
Qed.

Theorem (* 246 *) law_246 (*Left U ∨ strengthening*) (p q r : t) : (p U q) U r ⟹ (p ∨ q) U r.
Proof.
  apply impl_implies.
  rewrite <- (law_86 (p U q) (p ∨ q)).
  rewrite until_28.
  boolean.
  now rewrite law_64.
Qed.

Theorem (* 247 *) law_247 (*Left W ∨ strengthening*) (p q r : t) : (p W q) W r ⟹ (p ∨ q) W r.
Proof.
  apply impl_implies.
  rewrite <- (law_238 (p W q) (p ∨ q)).
  rewrite law_206.
  boolean.
  now rewrite law_64.
Qed.

Theorem (* 248 *) law_248 (*Right W ∨ strengthening*) (p q r : t) : p W (q W r) ⟹ p W (q ∨ r).
Proof.
  apply impl_implies.
  rewrite <- (law_239 (q W r) (q ∨ r) p).
  rewrite law_206.
  boolean.
  now rewrite law_64.
Qed.

Theorem (* 249 *) law_249 (*Right W ∨ ordering*) (p q r : t) : p W (q W r) ⟹ (p ∨ q) W r.
Proof.
  rewrite 2 wait_def.
  rewrite until_left_or.
  rewrite law_140.
  rewrite until_right_or_order.
  rewrite <- or_assoc.
  rewrite law_100.
  rewrite until_absorb_or_u.
  now rewrite <- wait_def.
Qed.

Theorem (* 250 *) law_250 (*Right ∧ W ordering*) (p q r : t) : p W (q ∧ r) ⟹ (p W q) W r.
Proof.
  rewrite (wait_def p q).
  rewrite <- law_185.
  rewrite 2 (wait_def _ r).
  rewrite law_72.
  rewrite <- !or_assoc.
  rewrite or_comm.
  rewrite <- !or_assoc.
  rewrite <- or_inj.
  rewrite <- or_inj.
  rewrite or_comm.
  rewrite <- until_right_and_order.
  now rewrite <- wait_def.
Qed.

Theorem (* 251 *) law_251 (*U ordering*) (p q : t) : ¬p U q ∨ ¬q U p ≈ ◇ (p ∨ q).
Proof.
  rewrite (law_196 _ q).
  rewrite (law_196 _ p).
  rewrite and_comm.
  rewrite <- until_left_or.
  rewrite <- not_or.
  rewrite law_192.
  now rewrite or_comm.
Qed.

Theorem (* 252 *) law_252 (*W ordering*) (p q : t) : ¬p W q ∨ ¬q W p ≈ ⊤.
Proof.
  rewrite (law_195 _ q).
  rewrite (law_195 _ p).
  rewrite and_comm.
  rewrite <- law_184.
  rewrite <- not_or.
  now rewrite law_191.
Qed.

Theorem (* 253 *) law_253 (*W implication ordering*) (p q r : t) : p W q ∧ ¬q W r ⟹ p W r.
Proof.
  assert (A : p U q ∧ □ ¬q ≈ ⊥).
    rewrite law_171.
    rewrite and_assoc.
    rewrite law_92.
    now boolean.

  assert (B : □ p ∧ □ ¬q ⟹ p W r).
    rewrite and_proj.
    now rewrite <- law_179.

  assert (C : □ p ∧ ¬q U r ⟹ p W r).
    rewrite and_proj.
    now rewrite <- law_179.

  rewrite 2 wait_def.
  rewrite and_or_r.
  rewrite and_or.
  rewrite and_or.
  rewrite A; boolean.
  rewrite B.
  rewrite C.
  rewrite until_impl_order.
  rewrite law_174.
  now boolean.
Qed.

Theorem (* 254 *) law_254 (*Lemmon formula*) (p q : t) : □ (□ p ⇒ q) ∨ □ (□ q ⇒ p) ≈ ⊤.
Proof.
  apply true_impl.
  (* rewrite !impl_def. *)
  rewrite <- (law_206 _ q).
  rewrite <- (law_206 _ p).
  rewrite <- !law_177.
  now rewrite law_252.
Qed.

Definition F (p q : t) := □ (p ⇒ □ q).

Theorem Dummett (p : t) : F (F p p) p ⟹ (◇ □ p ⇒ □ p).
Proof.
Abort.

(*** Release R *)

(*
Theorem law_256 (p q : t) : p U q ≈ ¬(¬p R ¬q).
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_257 (p q : t) : p W q ≈ q R (q ∨ p).
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_258 (p q : t) : p R q ≈ q W (q ∧ p).
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_259 (p q : t) : p R q ≈ q ∧ (p ∨ ◯ (p R q)).
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_260 (p q r : t) : p R (q ∨ r) ≈ (p R q) ∨ (p R r).
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_261 (p q r : t) : (p ∧ q) R r ≈ (p R r) ∧ (q R r).
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_262 (p q : t) : ◯ (p R q) ≈ ◯ p R ◯ q.
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_263 (p q : t) : □ q ≈ ⊥ R q.
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_264 (p q : t) : ¬(p U q) ≈ ¬p R ¬q.
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_265 (p q : t) : ¬(p R q) ≈ ¬p U ¬q.
Proof.
  (* FILL IN HERE *)
Admitted.

(*** Strong Release M *)

Theorem law_266 (p q : t) : p W q ≈ ¬(¬p M ¬q).
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_267 (p q : t) : p M q ≈ ¬(¬p W ¬q).
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_268 (p q : t) : p M q ≈ p R q ∧ ◇ p.
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_269 (p q : t) : p M q ≈ p R (q ∧ ◇ p).
Proof.
  (* FILL IN HERE *)
Admitted.

(*** OLD *)

Notation "p ≉ q" := (~ (p ≈ q)) (at level 90, no associativity).

Theorem law_270 (p q r : t) : □ (p ⇒ ¬q ∧ ◯ r) ⟹ p ⇒ ¬(q U r).
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_271 (p q r s : t) : □ ((p ⇒ q U r) ∧ (r ⇒ q U s)) ⟹ p ⇒ □ r.
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_272 (p q : t) : ◇ (p U q) ≉ ◇ p U ◇ q.
Proof.
  (* FILL IN HERE *)
Admitted.

Theorem law_273 (p q : t) : ¬◇ (¬p ∧ q) ≈ □ (p ∨ ¬q).
Proof.
  (* FILL IN HERE *)
Admitted.

(* Definition examine {a : Type} (P : a -> t) : t := fun s => P (head s) s. *)
*)

End LinearTemporalLogicFacts.
