(** Principles of negation *)

Lemma not_next (φ : LTL) : ¬(◯ φ) ≈ ◯ ¬φ.
Proof. split; repeat intro; auto. Qed.

Lemma until_incl_not_release (φ ψ : LTL) : Included _ (φ U ψ) (¬ (¬φ R ¬ψ)).
Proof.
  repeat intro.
  unfold In in *.
  dependent induction H.
  + dependent induction H0.
    * contradiction.
    * contradiction.
  + apply release_inv in H1.
    destruct H1.
    destruct H2.
    * contradiction.
    * rewrite tail_cons in H2.
      intuition.
Qed.

Lemma release_incl_not_until (φ ψ : LTL) : Included _ (¬φ R ¬ψ) (¬ (φ U ψ)).
Proof.
  repeat intro.
  unfold In in *.
  dependent induction H.
  + dependent induction H1.
    * contradiction.
    * contradiction.
  + apply until_inv in H1.
    destruct H1.
    * contradiction.
    * destruct H1.
      rewrite tail_cons in H2.
      intuition.
Qed.

Lemma not_until (φ ψ : LTL) : ¬ (φ U ψ) ≈ ¬φ R ¬ψ.
Proof.
  split; repeat intro; unfold In in *.
  - admit.
  - apply release_incl_not_until in H.
    contradiction.
Abort.

Lemma not_release (φ ψ : LTL) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Abort.

Lemma not_top : ¬(⊤) ≈ ⊥.
Proof.
  split; repeat intro.
  - elimtype False.
    apply H.
    now constructor.
  - unfold In in *.
    contradiction H.
Qed.

Lemma not_bottom : ¬(⊥) ≈ ⊤.
Proof.
  split; repeat intro.
  - now constructor.
  - contradiction H0.
Qed.

Lemma not_eventually (φ : LTL) : ¬(◇ φ) ≈ □ ¬φ.
Proof. now rewrite not_until, not_top. Qed.

Lemma not_always (φ : LTL) : ¬(□ φ) ≈ ◇ ¬φ.
Proof. now rewrite not_release, not_bottom. Qed.

Lemma not_weakUntil (φ ψ : LTL) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Proof.
  unfold weakUntil, strongRelease.
  rewrite not_or, not_always.
  now rewrite <- not_until.
Qed.

Lemma not_strongRelease (φ ψ : LTL) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Proof.
  unfold weakUntil, strongRelease.
  rewrite not_and, not_eventually.
  now rewrite <- not_release.
Qed.

(** Boolean equivalences *)

Lemma or_comm (φ ψ : LTL) : φ ∨ ψ ≈ ψ ∨ φ.
Proof. split; repeat intro; destruct H; now intuition. Qed.

Lemma or_assoc (φ ψ χ : LTL) : φ ∨ (ψ ∨ χ) ≈ (φ ∨ ψ) ∨ χ.
Proof.
  split; repeat intro.
  - destruct H.
    + now left; left.
    + destruct H.
      * now left; right.
      * now right.
  - destruct H.
    + destruct H.
      * now left.
      * now right; left.
    + now right; right.
Qed.

Lemma or_bottom (φ : LTL) : φ ∨ (⊥) ≈ φ.
Proof.
  split; repeat intro.
  - destruct H; auto.
    contradiction H.
  - now left.
Qed.

Lemma bottom_or (φ : LTL) : (⊥) ∨ φ ≈ φ.
Proof.
  split; repeat intro.
  - destruct H; auto.
    contradiction H.
  - now right.
Qed.

Lemma or_and (φ ψ χ : LTL) : φ ∨ (ψ ∧ χ) ≈ (φ ∨ ψ) ∧ (φ ∨ χ).
Proof.
  split; repeat intro.
  - destruct H.
    + split; now left.
    + destruct H; intuition.
  - destruct H.
    destruct H, H0; intuition.
Qed.

Lemma and_comm (φ ψ : LTL) : φ ∧ ψ ≈ ψ ∧ φ.
Proof.
  split; repeat intro.
  - destruct H.
    split; auto.
  - destruct H.
    split; auto.
Qed.

Lemma and_assoc (φ ψ χ : LTL) : φ ∧ (ψ ∧ χ) ≈ (φ ∧ ψ) ∧ χ.
Proof.
  split; repeat intro.
  - now destruct H, H0.
  - now destruct H, H.
Qed.

Lemma and_top (φ : LTL) : φ ∧ (⊤) ≈ φ.
Proof.
  split; repeat intro.
  - now destruct H.
  - now split.
Qed.

Lemma top_and (φ : LTL) : (⊤) ∧ φ ≈ φ.
Proof.
  split; repeat intro.
  - now destruct H.
  - now split.
Qed.

Lemma and_or (φ ψ χ : LTL) : φ ∧ (ψ ∨ χ) ≈ (φ ∧ ψ) ∨ (φ ∧ χ).
Proof.
  split; repeat intro.
  - destruct H, H0.
    + now left.
    + now right.
  - destruct H, H.
    + split; auto.
      now left.
    + split; auto.
      now right.
Qed.

(** Temporal equivalences *)

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof. reflexivity. Qed.

Lemma until_eventually (φ ψ : LTL) s : (φ U ψ) s -> (◇ ψ) s.
Proof.
  intros.
  dependent induction H; intuition.
  - now left.
  - right.
    + now constructor.
    + exact IHuntil.
Qed.

Lemma always_is (φ : LTL) s : (□ φ) s -> φ s.
Proof.
  intros.
  dependent induction H; intuition.
Qed.

Lemma always_tail (φ : LTL) s : (□ φ) s -> (□ φ) (tail s).
Proof.
  repeat intro.
  apply release_inv in H.
  now intuition.
Qed.

Lemma always_cons (φ : LTL) x s : (□ φ) (Cons x s) -> (□ φ) s.
Proof.
  repeat intro.
  apply release_cons_inv in H.
  now intuition.
Qed.

Lemma eventually_tail (φ : LTL) s : (◇ φ) s -> φ s \/ (◇ φ) (tail s).
Proof.
  intros.
  dependent induction H; intuition.
Qed.

Lemma eventually_cons (φ : LTL) x s : (◇ φ) (Cons x s) -> φ (Cons x s) \/ (◇ φ) s.
Proof.
  intros.
  dependent induction H; intuition.
Qed.

Lemma eventually_always_until (φ ψ : LTL) s :
  (◇ ψ) s -> (□ φ) s -> (φ U ψ) s.
Proof.
  intros.
  dependent induction H; intuition.
  - now left.
  - clear H.
    right.
    + now apply always_is.
    + apply IHuntil.
      now apply always_cons in H1.
Qed.

(* ψ always remains true *)
Lemma always_release (ψ : LTL) : □ ψ ≈ ⊥ R ψ.
Proof. reflexivity. Qed.

Lemma always_not_eventually (ψ : LTL) : □ ψ ≈ ¬◇ ¬ψ.
Proof.
  now rewrite <- not_bottom, not_until, <- not_top, !Complement_Complement.
Qed.

Lemma release_until (φ ψ : LTL) : φ R ψ ≈ ¬(¬φ U ¬ψ).
Proof. now rewrite not_until, !Complement_Complement. Qed.

Lemma weakUntil_release_or (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Abort.

Lemma release_weakUntil_and (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Abort.

Lemma weakUntil_until_or (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Abort.

Lemma strongRelease_not_weakUntil (φ ψ : LTL) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Abort.

Lemma strongRelease_and_release (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Abort.

Lemma strongRelease_release_and (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Abort.

Lemma until_eventually_weakUntil (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof.
  rewrite weakUntil_until_or.
  split; repeat intro.
  - induction H.
    + split.
      * now left.
      * now left; left.
    + destruct IHuntil.
      split.
      * right; auto.
        now constructor.
      * now right.
  - destruct H.
    unfold In in H0.
    dependent induction H0.
    + destruct H0.
      * now left.
      * now apply eventually_always_until.
    + unfold In in H.
      apply until_cons_inv in H.
      destruct H; intuition.
      * now left.
      * right; auto.
Qed.

(** Distributivity *)

Lemma next_top : ◯ (⊤) ≈ ⊤.
Proof. split; repeat intro; constructor. Qed.

Lemma next_bottom : ◯ (⊥) ≈ ⊥.
Proof. split; repeat intro; contradiction. Qed.

Lemma next_or (φ ψ : LTL) : ◯ (φ ∨ ψ) ≈ (◯ φ) ∨ (◯ ψ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - inversion H; subst.
    + left; auto.
    + right; auto.
  - inversion H; subst.
    + left; auto.
    + right; auto.
Qed.

Lemma next_and (φ ψ : LTL) : ◯ (φ ∧ ψ) ≈ (◯ φ) ∧ (◯ ψ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - inversion H; subst.
    now split.
  - inversion H; subst.
    now split.
Qed.

Lemma p_cons_tail (φ : LTL) s :
  φ (tail s) <-> exists x u, s = Cons x u /\ φ u.
Proof.
  split; intros.
  - exists (head s).
    exists (tail s).
    split; auto.
    now rewrite cons_head_tail.
  - destruct H, H, H; subst.
    now rewrite tail_cons.
Qed.

Lemma next_until (φ ψ : LTL) : ◯ (φ U ψ) ≈ (◯ φ) U (◯ ψ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - apply p_cons_tail in H.
    destruct H, H, H; subst.
    generalize dependent x0.
    dependent induction H0.
    + now left.
    + right.
      * now rewrite tail_cons.
      * apply IHuntil.
  - dependent induction H.
    + now left.
    + rewrite tail_cons in *.
      apply p_cons_tail in IHuntil.
      destruct IHuntil, H1, H1; subst.
      right; auto.
Qed.

Lemma next_release (φ ψ : LTL) : ◯ (φ R ψ) ≈ (◯ φ) R (◯ ψ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - apply p_cons_tail in H.
    destruct H, H, H; subst.
    generalize dependent x0.
    dependent induction H0.
    + now left.
    + right.
      * now rewrite tail_cons.
      * apply IHrelease.
  - dependent induction H.
    + now left.
    + rewrite tail_cons in *.
      apply p_cons_tail in IHrelease.
      destruct IHrelease, H1, H1; subst.
      right; auto.
Qed.

Lemma next_eventually (φ : LTL) : ◯ (◇ φ) ≈ ◇ (◯ φ).
Proof. now rewrite next_until, next_top. Qed.

Lemma next_always (φ : LTL) : ◯ (□ φ) ≈ □ (◯ φ).
Proof. now rewrite next_release, next_bottom. Qed.

Lemma until_or (ρ φ ψ : LTL) : ρ U (φ ∨ ψ) ≈ (ρ U φ) ∨ (ρ U ψ).
Proof.
  split; repeat intro; unfold In in *.
  - dependent induction H.
    + destruct H.
      * now left; left.
      * now right; left.
    + destruct IHuntil.
      * now left; right.
      * now right; right.
  - destruct H.
    + induction H.
      * now left; left.
      * now right.
    + induction H.
      * now left; right.
      * now right.
Qed.

Lemma and_until (ρ φ ψ : LTL) : (φ ∧ ψ) U ρ ≈ (φ U ρ) ∧ (ψ U ρ).
Proof.
  split; repeat intro; unfold In in *.
  - dependent induction H.
    + split.
      * now left.
      * now left.
    + inversion H; subst; clear H.
      destruct IHuntil.
      unfold In in *.
      * split.
        ** now right.
        ** now right.
  - destruct H.
    induction H.
    + now left.
    + apply until_cons_inv in H0.
      destruct H0.
      * now left.
      * destruct H0.
        right.
        ** now split.
        ** now apply IHuntil.
Qed.

Lemma release_or (ρ φ ψ : LTL) : ρ R (φ ∨ ψ) ≈ (ρ R φ) ∨ (ρ R ψ).
Proof.
  rewrite !release_until.
  rewrite <- not_and.
  rewrite until_or.
  split; repeat intro; unfold In in *.
  - dependent induction H.
    + destruct H.
      * now left; left.
      * now right; left.
    + inversion H; subst; clear H.
      destruct IHrelease;
      unfold In in *.
      * now left; right.
      * left. right; auto. left.
  - destruct H.
    + induction H.
      * left; auto.
        now left.
      * right.
        ** now left.
        ** exact IHrelease.
    + induction H.
      * left; auto.
        now right.
      * right; auto.
        now right.
Abort.

Lemma and_release (ρ φ ψ : LTL) : (φ ∧ ψ) R ρ ≈ (φ R ρ) ∧ (ψ R ρ).
Abort.

Lemma eventually_or (φ ψ : LTL) : ◇ (φ ∨ ψ) ≈ (◇ φ) ∨ (◇ ψ).
Proof. now rewrite until_or. Qed.

Lemma always_and (φ ψ : LTL) : □ (φ ∧ ψ) ≈ (□ φ) ∧ (□ ψ).
Proof.
  split; repeat intro; unfold In in *.
  - split; unfold In in *.
    + induction H; auto.
      * contradiction.
      * right.
        ** now destruct H.
        ** exact IHrelease.
    + induction H; auto.
      * contradiction.
      * right.
        ** now destruct H.
        ** exact IHrelease.
  - destruct H; unfold In in *.
    induction H.
    + contradiction.
    + revert IHrelease.
      apply release_cons_inv in H0.
      destruct H0.
      destruct H2.
      * contradiction.
      * intros.
        right.
        ** now split.
        ** now apply IHrelease.
Qed.

(** Special Temporal properties *)

Lemma until_idempotent_left  (φ ψ : LTL) : (φ U ψ) U ψ ≈ φ U ψ.
Proof.
  split; repeat intro.
  - induction H; auto.
    now left.
  - unfold In in *.
    dependent induction H.
    + now left.
    + right; auto.
      now right; auto.
Qed.

Lemma until_idempotent_right (φ ψ : LTL) : φ U (φ U ψ) ≈ φ U ψ.
Proof.
  split; repeat intro.
  - induction H; auto.
    now right.
  - unfold In in *.
    dependent induction H.
    + now left; left.
    + right; auto.
Qed.

Lemma eventually_idempotent (φ : LTL) : ◇ ◇ φ ≈ ◇ φ.
Proof. apply until_idempotent_right. Qed.

Lemma always_idempotent (φ : LTL) : □ □ φ ≈ □ φ.
Proof.
  rewrite !always_not_eventually.
  rewrite Complement_Complement.
  now rewrite eventually_idempotent.
Qed.

(** Expansion laws *)

Lemma expand_until (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ ◯ (φ U ψ)).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - dependent induction H.
    + now left.
    + right.
      split.
      * exact H.
      * unfold In.
        now rewrite tail_cons.
  - destruct H.
    + now left.
    + destruct H; unfold In in *.
      rewrite <- cons_head_tail.
      right; auto.
      now rewrite cons_head_tail.
Qed.

Lemma expand_release (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - dependent induction H.
    + split; auto.
      now left.
    + split; auto.
      right.
      unfold In.
      now rewrite tail_cons.
  - destruct H, H0; unfold In in *.
    + now left.
    + rewrite <- cons_head_tail.
      right; auto.
      now rewrite cons_head_tail.
Qed.

Lemma expand_always (φ : LTL) : □ φ ≈ φ ∧ ◯ (□ φ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - split.
    + now apply always_is.
    + unfold In.
      now apply always_tail.
  - destruct H.
    unfold In in *.
    apply p_cons_tail in H0.
    destruct H0, H0, H0; subst.
    now right.
Qed.

Lemma expand_eventually (φ : LTL) : ◇ φ ≈ φ ∨ ◯ (◇ φ).
Proof.
  unfold next.
  split; repeat intro; unfold In in *.
  - apply until_inv in H.
    destruct H.
    + now left.
    + destruct H.
      now right.
  - destruct H.
    + now left.
    + unfold In in H.
      apply p_cons_tail in H.
      destruct H, H, H; subst.
      now right.
Qed.

Lemma expand_weakUntil  (φ ψ : LTL) : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).
Proof.
  unfold next, weakUntil.
  split; repeat intro; unfold In in *.
  - destruct H; unfold In in *.
    dependent induction H.
    + now left.
    + destruct IHuntil.
      * right.
        split; auto.
        unfold In in *.
        rewrite tail_cons.
        now left.
      * right.
        split; auto.
        unfold In in *.
        rewrite tail_cons.
        now left.
    + right.
      split; auto.
      * now apply always_is.
      * unfold In.
        right.
        now apply always_tail.
  - destruct H.
    + now left; left.
    + destruct H.
      inversion H0; subst; clear H0.
      unfold In in *.
      * left.
        rewrite <- cons_head_tail.
        right; auto.
        now rewrite cons_head_tail.
      * right.
        now apply expand_always.
Qed.

(** Absorption laws *)

Lemma asborb_eventually (φ : LTL) : ◇ □ ◇ φ ≈ □ ◇ φ.
Abort.

Lemma asborb_always (φ : LTL) : □ ◇ □ φ ≈ ◇ □ φ.
Abort.

(** Predicates on elements *)

Definition examine (P : a -> LTL) : LTL := fun s => P (head s) s.

Global Program Instance examine_Same_set :
  Proper ((@eq a ==> Same_set Stream) ==> Same_set Stream) examine.
Next Obligation.
  intros.
  unfold respectful in H.
  split; repeat intro; unfold In, examine in *;
  specialize (H (head x0) (head x0) (reflexivity _));
  now apply H.
Qed.

Inductive release (p q : LTL) : LTL :=
  | release_hd s : q s -> p s -> release p q s
  | release_tl x s : q (Cons x s) -> release p q s -> release p q (Cons x s).

Notation "p 'R' q" := (release p q) (at level 45).

Global Program Instance release_Same_set :
  Proper (Same_set Stream ==> Same_set Stream ==> Same_set Stream) release.
Next Obligation.
  intros.
  split; repeat intro; unfold In in *.
  - induction H1.
    + left.
      * now apply H0.
      * now apply H.
    + right; auto.
      now apply H0.
  - induction H1.
    + left.
      * now apply H0.
      * now apply H.
    + right; auto.
      now apply H0.
Qed.

Lemma release_inv (p q : LTL) s :
  release p q s -> q s /\ (p s \/ release p q (tail s)).
Proof.
  intros.
  dependent induction H; intuition.
Qed.

Lemma release_cons_inv (p q : LTL) x s :
  release p q (Cons x s) -> q (Cons x s) /\ (p (Cons x s) \/ release p q s).
Proof.
  intros.
  dependent induction H; intuition;
  apply cons_inj in x;
  destruct x; subst; auto.
Qed.

Definition strongRelease (p q : LTL) := (p R q) ∧ ◇ p.
Notation "p 'M' q" := (strongRelease p q) (at level 45).
