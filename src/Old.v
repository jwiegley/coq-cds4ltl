(* DeMorgan's laws *)
Lemma not_or (φ ψ : LTL) : ¬ (φ ∨ ψ) ≈ ¬ φ ∧ ¬ ψ.
Proof.
  split.
  - intros s NAB.
    split.
    + intro.
      apply NAB.
      left; auto.
    + intro.
      apply NAB.
      right; auto.
  - intros s NAB.
    intro.
    induction NAB.
    destruct H.
    + apply H0; auto.
    + apply H1; auto.
Qed.

Lemma not_and (φ ψ : LTL) : ¬ (φ ∧ ψ) ≈ ¬ φ ∨ ¬ ψ.
Proof.
  split.
  - rewrite <- Complement_Complement.
    intros s NAB.
    intro H.
    apply NAB.
    split.
    + rewrite <- (Complement_Complement _ φ).
      intro H0.
      apply H.
      left; auto.
    + rewrite <- (Complement_Complement _ ψ).
      intro H0.
      apply H.
      right; auto.
  - intros s NANB AB.
    destruct AB as [A1 B1].
    destruct NANB as [s NA | s NB]; auto.
Qed.

Lemma next_inv (p : LTL) (s : Stream a) :
  next p s -> exists x s', stream_eq a s (Cons x s') /\ p s'.
Proof.
  unfold next, tail.
  intros.
  exists (head s).
  exists (tail s).
  split.
  - unfold head, tail; intros.
    now destruct s.
  - exact H.
Qed.

Lemma next_cons_inv (p : LTL) x s : next p (Cons x s) <-> p s.
Proof. now unfold next, tail. Qed.

Global Program Instance until_Same_set :
  Proper (Same_set (Stream a) ==> Same_set (Stream a)
                              ==> Same_set (Stream a)) until.
Next Obligation.
  intros.
  split; repeat intro; unfold In in *.
  - destruct H1, H1.
    exists x2.
    split.
    + now apply H0.
    + intros.
      now apply H, H2.
  - destruct H1, H1.
    exists x2.
    split.
    + now apply H0.
    + intros.
      now apply H, H2.
Qed.

Global Program Instance until_Same_set_iff (p q : LTL) :
  Proper (stream_eq a ==> iff) p ->
  Proper (stream_eq a ==> iff) q ->
  Proper (stream_eq a ==> iff) (until p q).
Next Obligation.
  unfold until.
  split; repeat intro.
  - destruct H2, H2.
    exists x0.
    split.
    + now setoid_rewrite <- H1.
    + intros.
      setoid_rewrite <- H1.
      now apply H3.
  - destruct H2, H2.
    exists x0.
    split.
    + now setoid_rewrite H1.
    + intros.
      setoid_rewrite H1.
      now apply H3.
Qed.

Lemma until_inv (p q : LTL) s :
  until p q s -> q s \/ (p s /\ until p q (tail s)).
Proof.
  intros.
  dependent induction H; intuition.
Admitted.

Lemma until_cons_inv (p q : LTL) x s :
  until p q (Cons x s) -> q (Cons x s) \/ (p (Cons x s) /\ until p q s).
Proof.
  intros.
  dependent induction H; intuition.
Admitted.

Definition weakUntil (p q : LTL) := (p U q) ∨ □ p.
Notation "p 'W' q" := (weakUntil p q) (at level 40).

Definition release (p q : LTL) := ¬(¬p U ¬q).
Notation "p 'R' q" := (release p q) (at level 40).

Definition strongRelease (p q : LTL) := (p R q) ∧ ◇ p.
Notation "p 'M' q" := (strongRelease p q) (at level 40).

(*************************************************************************
 * Laws for the Linear Temporal Logic
 *)

Ltac solve :=
  repeat
    (match goal with
     | [ H : () |- _ ] => destruct H
     | [ |- _ ≈ _ ] => split; repeat intro

     | [ H : (_ ∧ _) _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- (_ ∧ _) _ ] => split

     | [ H : (_ ∨ _) _ |- _ ] =>
       let H1 := fresh "H" in inversion H as [H1|H1]; subst; clear H
     | [ H : ?P _ |- (?P ∨ _) _ ] => now left
     | [ H : ?P _ |- (_ ∨ ?P) _ ] => now right
     | [ H : ?P _ |- ((?P ∨ _) ∨ _) _ ] => now left; left
     | [ H : ?P _ |- ((_ ∨ ?P) ∨ _) _ ] => now left; right
     | [ H : ?P _ |- (_ ∨ (?P ∨ _)) _ ] => now right; left
     | [ H : ?P _ |- (_ ∨ (_ ∨ ?P)) _ ] => now right; right
     | [ H : ¬ ?P _ |- (¬ ?P ∨ _) _ ] => now left
     | [ H : ¬ ?P _ |- (_ ∨ ¬ ?P) _ ] => now right
     | [ H : ¬ ?P _ |- ((¬ ?P ∨ _) ∨ _) _ ] => now left; left
     | [ H : ¬ ?P _ |- ((_ ∨ ¬ ?P) ∨ _) _ ] => now left; right
     | [ H : ¬ ?P _ |- (_ ∨ (¬ ?P ∨ _)) _ ] => now right; left
     | [ H : ¬ ?P _ |- (_ ∨ (_ ∨ ¬ ?P)) _ ] => now right; right

     | [ H1 : ?P _, H2 : ?Q _ |- ((?P ∧ ?Q) ∨ _) _ ] => left
     | [ H1 : ?P _, H2 : ?Q _ |- (_ ∨ (?P ∧ ?Q)) _ ] => right

     | [ H : ¬ (_ ∨ _) _ |- _ ] => apply not_or in H
     | [ H : ¬ (_ ∧ _) _ |- _ ] => apply not_and in H

     | [ H : _ /\ _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- _ /\ _ ] => split

     | [ H : _ \/ _ |- _ ] =>
       let H1 := fresh "H" in inversion H as [H1|H1]; subst; clear H

     | [ H : (_ ↔ _) _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- (_ ↔ _) _ ] => split

     | [ |- _ -> _ ] => intro
     | [ H: ?P |- ?P ] => apply H

     | [ H : ?P ≈ ?Q |- _ ] => rewrite H in *; clear H

     | [ H : _ <-> _ |- _ ] =>
       let H1 := fresh "H" in
       let H2 := fresh "H" in inversion H as [H1 H2]; subst; clear H
     | [ |- _ <-> _ ] => split

     | [ H1 : ?P, H2 : ~ ?P |- _ ] => contradiction
     | [ H1 : ?P _, H2 : ¬ ?P _ |- _ ] => contradiction

     | [ H : (⊥) _ |- _ ] => contradiction
     | [ H : ¬ (⊤) _ |- False ] => apply H

     | [ |- (⊤) _ ] => now constructor
     | [ |- ¬ _ _ ] => intro
     | [ |- (⊥) _ ] => elimtype False
     | [ |- ~ _ ] => intro
     | [ H : ¬ (fun _ => forall _, _) _ |- _ ] => unfold Complement, In in H

     | [ |- ◯ _ _ ] => unfold next

     | [ |- nat ] => exact 0

     | [ H : ~ (forall _, ~ _)        |- _ ] => apply not_all_not_ex in H
     | [ H : (forall _, ~ _) -> False |- _ ] => apply not_all_not_ex in H
     | [ H : ~ (forall _, _)          |- _ ] => apply not_all_ex_not in H
     | [ H : (forall _, _) -> False   |- _ ] => apply not_all_ex_not in H
     | [ H : ~ (exists _, ~ _)        |- _ ] => apply not_ex_not_all in H
     | [ H : (exists _, ~ _) -> False |- _ ] => apply not_ex_not_all in H
     | [ H : ~ (exists _, _)          |- _ ] => apply not_ex_all_not in H
     | [ H : (exists _, _) -> False   |- _ ] => apply not_ex_all_not in H

     | [ |- exists _, ¬ _ _ ] => apply not_all_ex_not; intro

     | [ H : forall i : nat, ?P (from i ?S) |- ?P ?S ] => apply (H 0)
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (tail ?S) ] => apply (H 1)
     | [ H : ?P ?S |- exists i : nat, ?P (from i ?S) ] => exists 0
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (from ?I (tail ?S)) ]
         => rewrite from_tail_S; apply H
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (tail (from ?I ?S)) ]
         => rewrite tail_from_S; apply H
     | [ H : ?P (tail ?S) |- exists i : nat, ?P (from i ?S) ] => exists 1
     | [ H : forall i : nat, ?P (from i (from ?X ?S))
       |- exists n : nat, ?P (from n (from _ ?S)) ] => eexists; rewrite from_from
     | [ H : forall i : nat, ?P (from i (tail ?S)) |- ?P (tail (from _ ?S)) ] =>
       rewrite tail_from
     | [ H : forall i : nat, ?P (tail (from i ?S)) |- ?P (from _ (tail ?S)) ] =>
       rewrite from_tail
     | [ H : forall i j : nat, ?P (from j (from i ?S)) |- ?P (from _ ?S) ] =>
       apply (H 0)
     | [ H : forall i : nat, ?P (from i ?S) |- ?P (from ?I (from ?J ?S)) ] =>
       rewrite from_plus
     | [ H : ?P (from ?I (from ?J ?S)) |- exists i : nat, ?P (from i ?S) ] =>
       rewrite from_plus in H
     | [ H : ?P (from ?I ?S) |- exists i : nat, ?P (from i ?S) ] => exists I
     | [ H : ?P (from ?I ?S) |- exists i j : nat, ?P (from i (from j ?S)) ] =>
       exists I; exists 0
     | [ H : ?P (from ?I ?S) |- exists i j : nat, ?P (from j (from i ?S)) ] =>
       exists I; exists 0
     | [ H : ?P (tail (from ?I ?S)) |- exists i : nat, ?P (from i (tail ?S)) ] =>
       exists I; rewrite from_tail
     | [ H : ?P (from ?I (tail ?S)) |- exists i : nat, ?P (tail (from i ?S)) ] =>
       exists I; rewrite tail_from

     end;
     unfold In, next, until, any, every, release, weakUntil in *;
     intros;
     try rewrite !Complement_Complement in *;
     try unshelve intuition eauto;
     try unshelve firstorder eauto;
     try unshelve eauto;
     try (now left);
     try (now right);
     try (now left; left);
     try (now left; right);
     try (now right; left);
     try (now right; right)).

Lemma law_34 (φ : LTL) : forall s, ◇□ φ s -> □◇ φ s.
Lemma law_35 (φ : LTL) : forall s, □¬ φ s -> ¬□ φ s.

Lemma law_43 (φ : LTL) : ◇□◇ φ ≈ □◇ φ.
Lemma law_44 (φ : LTL) : □◇□ φ ≈ ◇□ φ.
Lemma law_45 (φ : LTL) : □◇□◇ φ ≈ □◇ φ.
Lemma law_46 (φ : LTL) : ◇□◇□ φ ≈ ◇□ φ.
Lemma law_47 (φ : LTL) : ◯□◇ φ ≈ □◇ φ.
Lemma law_48 (φ : LTL) : ◯◇□ φ ≈ ◇□ φ.

Lemma law_53 (φ ψ : LTL) : □ (φ ∧ ψ) ≈ □ φ ∧ □ ψ.
Lemma law_54 (φ ψ : LTL) : □ (φ ∨ ψ) ≉ □ φ ∨ □ ψ.
Lemma law_57 (φ ψ : LTL) : ◇ (φ ∧ ψ) ≉ ◇ φ ∧ ◇ ψ.
Lemma law_58 (φ ψ : LTL) : ◇ (φ ∨ ψ) ≉ ◇ φ ∨ ◇ ψ.
Lemma law_63 (φ ψ : LTL) : ◇□ (φ ∧ ψ) ≈ ◇□ φ ∧ ◇□ ψ.
Lemma law_64 (φ ψ : LTL) : □◇ (φ ∨ ψ) ≈ □◇ φ ∨ □◇ ψ.
Lemma law_65 (φ ψ : LTL) : ◇□ (φ → □ ψ) ≈ ◇□¬ φ ∧ ◇□ ψ.
Lemma law_66 (φ ψ : LTL) : □ (□◇ φ → ◇ ψ) ≈ ◇□¬ φ ∧ □◇ ψ.
Lemma law_67 (φ ψ : LTL) : □ ((φ ∨ □ ψ) ∧ (□ φ ∨ ψ)) ≈ □ φ ∨ □ ψ.
Lemma law_69 (φ : LTL) : □ φ ≈ ¬◇¬ φ.
Lemma law_70 (φ : LTL) : ◇ φ ∧ □¬ φ ≈ ⊥.
Lemma law_71 (φ : LTL) : □ φ ∧ ◇¬ φ ≈ ⊥.
Lemma law_72 (φ : LTL) : □ φ ∧ □¬ φ ≈ ⊥.
Lemma law_73 (φ : LTL) : □◇ φ ∧ ◇□¬ φ ≈ ⊥.
Lemma law_74 (φ : LTL) : ◇□ φ ∧ □◇¬ φ ≈ ⊥.
Lemma law_75 (φ : LTL) : ◇□ φ ∧ ◇□¬ φ ≈ ⊥.
Lemma law_76 (φ : LTL) : forall s, (◇ φ ∨ □¬ φ) s.
Lemma law_77 (φ : LTL) : forall s, (□ φ ∨ ◇¬ φ) s.
Lemma law_78 (φ : LTL) : forall s, (◇ φ ∨ ◇¬ φ) s.
Lemma law_79 (φ : LTL) : forall s, (□◇ φ ∨ ◇□¬ φ) s.
Lemma law_80 (φ : LTL) : forall s, (□◇ φ ∨ □◇¬ φ) s.
Lemma law_81 (φ : LTL) : forall s, (◇□ φ ∨ □◇¬ φ) s.
Lemma law_82 (φ ψ : LTL) : forall s, ◇ (φ → ψ) s -> (□ φ → ◇ ψ) s.
Lemma law_85 (φ ψ : LTL) : forall s, □ (φ → ψ) s -> (□ φ → □ ψ) s.
Lemma law_86 (φ ψ : LTL) : forall s, (□ φ ∨ □ ψ) s -> □ (φ ∨ ψ) s.
Lemma law_87 (φ ψ : LTL) : forall s, (□ φ ∧ ◇ ψ) s -> ◇ (φ ∧ ψ) s.
Lemma law_88 (φ ψ : LTL) : forall s, (◇ φ → ◇ ψ) s -> ◇ (φ → ψ) s.
Lemma law_90 (φ ψ : LTL) : forall s, □◇ (φ ∧ ψ) s -> (□◇ φ ∧ □◇ ψ) s.
Lemma law_91 (φ ψ : LTL) : forall s, □◇ (φ ∨ ψ) s -> (□◇ φ ∨ □◇ ψ) s.
Lemma law_92 (φ ψ : LTL) : forall s, ◇□ (φ ∧ ψ) s -> (◇□ φ ∧ ◇□ ψ) s.
Lemma law_93 (φ ψ : LTL) : forall s, (◇□ φ ∨ ◇□ ψ) s -> ◇□ (φ ∨ ψ) s.
Lemma law_94 (φ ψ : LTL) : forall s, (◇□ φ ∧ □◇ ψ) s -> □◇ (φ ∧ ψ) s.
Lemma law_95 (φ ψ : LTL) : forall s, (◇□ φ ∧ □ (□ φ → ◇ ψ)) s -> ◇ ψ s.
Lemma law_96 (φ ψ : LTL) : forall s, □ (φ → ψ) s -> (◯ φ → ◯ ψ) s.
Lemma law_97 (φ ψ : LTL) : forall s, □ (φ → ψ) s -> (◇ φ → ◇ ψ) s.
Lemma law_98 (φ ψ : LTL) : forall s, □ (φ → ψ) s -> (□◇ φ → □◇ ψ) s.
Lemma law_99 (φ ψ : LTL) : forall s, □ (φ → ψ) s -> (◇□ φ → ◇□ ψ) s.
Lemma law_100 (φ ψ : LTL) : forall s, □ φ s -> (◯ ψ → ◯ (φ ∧ ψ)) s.
Lemma law_101 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ → ◇ (φ ∧ ψ)) s.
Lemma law_102 (φ ψ : LTL) : forall s, □ φ s -> (□ ψ → □ (φ ∧ ψ)) s.
Lemma law_103 (φ ψ : LTL) : forall s, □ φ s -> (◯ ψ → ◯ (φ ∨ ψ)) s.
Lemma law_104 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ → ◇ (φ ∨ ψ)) s.
Lemma law_105 (φ ψ : LTL) : forall s, □ φ s -> (□ ψ → □ (φ ∨ ψ)) s.
Lemma law_106 (φ ψ : LTL) : forall s, □ φ s -> (◯ ψ → ◯ (φ → ψ)) s.
Lemma law_107 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ → ◇ (φ → ψ)) s.
Lemma law_108 (φ ψ : LTL) : forall s, □ φ s -> (□ ψ → □ (φ → ψ)) s.
Lemma law_109 (φ ψ : LTL) : forall s, □ (□ φ → ψ) s -> (□ φ → □ ψ) s.
Lemma law_110 (φ ψ : LTL) : forall s, □ (φ → ◇ψ) s -> (◇ φ → ◇ ψ) s.
Lemma law_112 (φ ψ : LTL) : forall s, □ (φ → ◯ ψ) s -> (φ → ◇ ψ) s.
Lemma law_113 (φ : LTL) : forall s, □ (φ → ◯¬ φ) s -> (φ → ¬□ φ) s.
Lemma law_115 (φ ψ : LTL) : forall s, □ (φ ∨ ◯ ψ → ψ) s -> (◇ φ → ψ) s.
Lemma law_116 (φ ψ : LTL) : forall s, □ (φ → ◯ φ ∧ ψ) s -> (φ → □ ψ) s.
Lemma law_117 (φ ψ χ : LTL) : forall s, □ (φ → (◯ φ ∧ ψ) ∨ χ) s -> (φ → □ ψ ∨ (ψ U χ)) s.
Lemma law_118 (φ ψ : LTL) : forall s, □ (φ → ◯ (φ ∨ ψ)) s -> (φ → □ φ ∨ (φ U ψ)) s.
Lemma law_119 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ψ) ∧ (ψ → ◯ χ) ∧ (χ → ρ)) s -> (φ → ◯ ρ) s.
Lemma law_120 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ψ) ∧ (ψ → ◇ χ) ∧ (χ → ρ)) s -> (φ → ◇ ρ) s.
Lemma law_121 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ψ) ∧ (ψ → □ χ) ∧ (χ → ρ)) s -> (φ → □ ρ) s.
Lemma law_122 (φ ψ χ : LTL) : forall s, □ ((φ → ◇ ψ) ∧ (ψ → ◇ χ)) s -> (φ → ◇ χ) s.
Lemma law_123 (φ ψ χ : LTL) : forall s, □ ((φ → □ ψ) ∧ (ψ → □ χ)) s -> (φ → □ χ) s.
Lemma law_124 (φ ψ χ : LTL) : forall s, (□ (□ φ → ◇ ψ) ∧ (ψ → ◯ χ)) s -> (□ φ → ◯□◇ χ) s.
Lemma law_125 (φ ψ : LTL) : forall s, □ (φ ∨ ψ) s -> exists u, □ ((φ ∧ u) ∨ (ψ ∧ ¬ u)) s.
Lemma law_126 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ◇ (ψ ∨ χ)) ∧ (ψ → ◇ ρ) ∧ (χ → ◇ ρ)) s -> (φ → ◇ ρ) s.
Lemma law_127 (φ ψ : LTL) : forall s, (□ (□ φ → ψ) ∨ □ (□ ψ → φ)) s.
Lemma law_128 (φ : LTL) : φ U (⊥) ≈ ⊥.
Lemma law_132 (φ : LTL) : ¬ φ U φ ≈ ◇ φ.
Lemma law_133 (φ ψ : LTL) : forall s, ψ s -> (φ U φ) s.
Lemma law_134 (φ ψ : LTL) : forall s, (φ U ψ) s -> (φ ∨ ψ) s.
Lemma law_135 (φ ψ : LTL) : forall s, (φ ∧ ψ) s -> (φ U ψ) s.
Lemma law_136 (φ ψ : LTL) : forall s, ((φ U ψ) ∨ (φ U ¬ ψ)) s.
Lemma law_137 (φ ψ : LTL) : φ ∨ (φ U ψ) ≈ φ ∨ ψ.
Lemma law_138 (φ ψ : LTL) : (φ U ψ) ∨ ψ ≈ φ U ψ.
Lemma law_139 (φ ψ : LTL) : (φ U ψ) ∧ ψ ≈ ψ.
Lemma law_140 (φ ψ : LTL) : (φ U ψ) ∨ (φ ∧ ψ) ≈ φ U ψ.
Lemma law_141 (φ ψ : LTL) : (φ U ψ) ∧ (φ ∨ ψ) ≈ φ U ψ.
Lemma law_142 (φ ψ : LTL) : φ U (φ U ψ) ≈ φ U ψ.
Lemma law_143 (φ ψ : LTL) : (φ U ψ) U ψ ≈ φ U ψ.
Lemma law_144 (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ ◯ (φ U ψ)).
Lemma law_145 (φ ψ : LTL) : φ U ψ ≈ (φ ∨ ψ) U ψ.
Lemma law_146 (φ ψ : LTL) : φ U ψ ≈ (φ ∧ ¬ ψ) U ψ.
Lemma law_147 (φ ψ χ : LTL) : φ U (ψ ∨ χ) ≈ (φ U ψ) ∨ (φ U χ).
Lemma law_148 (φ ψ χ : LTL) : forall s, ((φ U χ) ∨ (ψ U χ)) s -> ((φ ∨ ψ) U χ) s.
Lemma law_149 (φ ψ χ : LTL) : (φ ∧ ψ) U χ ≈ (φ U χ) ∧ (ψ U χ).
Lemma law_150 (φ ψ χ : LTL) : forall s, (φ U (ψ ∧ χ)) s -> ((φ U ψ) ∧ (φ U χ)) s.
Lemma law_151 (φ ψ χ : LTL) : forall s, (φ U (ψ ∧ χ)) s -> (φ U (ψ U χ)) s.
Lemma law_152 (φ ψ χ : LTL) : forall s, ((φ ∧ ψ) U χ) s -> ((φ U ψ) U χ) s.
Lemma law_153 (φ ψ χ : LTL) : forall s, ((φ ∧ ψ) U χ) s -> (φ U (ψ U χ)) s.
Lemma law_154 (φ ψ : LTL) : ◯ (φ U ψ) ≈ (◯ φ) U (◯ ψ).
Lemma law_155 (φ ψ : LTL) : ◇ (φ U ψ) ≉ (◇ φ) U (◇ ψ).
Lemma law_156 (φ : LTL) : ◇ φ ≈ ⊤ U φ.
Lemma law_160 (φ : LTL) : φ U □ φ ≈ □ φ.
Lemma law_161 (φ ψ : LTL) : φ U □ ψ ≈ □ (φ U ψ).
Lemma law_162 (φ ψ : LTL) : forall s, (◇ φ → ((φ → ψ) U φ)) s.
Lemma law_163 (φ ψ χ : LTL) : forall s, ((φ U ψ) ∧ (¬ ψ U χ)) s -> (φ U χ) s.
Lemma law_164 (φ ψ χ : LTL) : forall s, (φ U (ψ U χ)) s -> ((φ ∨ ψ) U χ) s.
Lemma law_165 (φ ψ χ : LTL) : forall s, ((φ → ψ) U χ) s -> ((φ U χ) → (ψ U χ)) s.
Lemma law_166 (φ ψ χ : LTL) : forall s, ((¬ φ U (ψ U χ)) ∧ (φ U χ)) s -> (ψ U χ) s.
Lemma law_167 (φ ψ χ : LTL) : forall s, ((φ U (¬ ψ U χ)) ∧ (ψ U χ)) s -> (φ U χ) s.
Lemma law_168 (φ ψ : LTL) : forall s, ((φ U ψ) ∧ (¬ ψ U φ)) s -> φ s.
Lemma law_169 (φ ψ : LTL) : forall s, (φ ∧ (¬ φ U ψ)) s -> ψ s.
Lemma law_170 (φ ψ : LTL) : forall s, □ φ s -> (◯ ψ → ◯ (φ U ψ)) s.
Lemma law_171 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ → ◇ (φ U ψ)) s.
Lemma law_172 (φ ψ : LTL) : forall s, □ φ s -> (□ ψ → □ (φ U ψ)) s.
Lemma law_174 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ) s -> (φ U ψ) s.
Lemma law_176 (φ ψ χ : LTL) : forall s, □ (φ → ψ) s -> ((χ U φ) → (χ U ψ)) s.
Lemma law_177 (φ ψ χ : LTL) : forall s, □ (φ → ψ) s -> ((φ U χ) → (ψ U χ)) s.
Lemma law_179 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ψ U χ) ∧ (χ → ψ U ρ)) s -> (φ → □ χ) s.
Lemma law_180 (φ ψ χ ρ : LTL) : forall s, □ ((φ → χ) ∧ (ψ → ρ)) s -> (φ U ψ → χ U ρ) s.
Lemma law_181 (φ ψ χ : LTL) : forall s, □ (φ → ¬ ψ ∧ ◯ χ) s -> (φ → ¬(ψ U χ)) s.

Lemma law_182 (φ : LTL) : φ W φ ≈ φ.
Lemma law_183 (φ ψ : LTL) : φ W ψ ≈ (φ U ψ) ∨ □ φ.
Lemma law_184 (φ ψ : LTL) : ¬(φ W ψ) ≈ ¬ ψ U (¬ φ ∧ ¬ ψ).
Lemma law_185 (φ ψ : LTL) : ¬(φ W ψ) ≈ (φ ∧ ¬ ψ) U (¬ φ ∧ ¬ ψ).
Lemma law_186 (φ ψ : LTL) : ¬(φ U ψ) ≈ ¬ ψ W (¬ φ ∧ ¬ ψ).
Lemma law_187 (φ ψ : LTL) : ¬(φ U ψ) ≈ (φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ).
Lemma law_188 (φ ψ : LTL) : ¬(¬ φ U ¬ ψ) ≈ ψ W (φ ∧ ψ).
Lemma law_189 (φ ψ : LTL) : ¬(¬ φ U ¬ ψ) ≈ (¬ φ ∧ ψ) W (φ ∧ ψ).
Lemma law_190 (φ ψ : LTL) : ¬(¬ φ W ¬ ψ) ≈ ψ U (φ ∧ ψ).
Lemma law_191 (φ ψ : LTL) : ¬(¬ φ W ¬ ψ) ≈ (¬ φ ∧ ψ) U (φ ∧ ψ).
Lemma law_192 (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Lemma law_193 (φ ψ : LTL) : φ W ψ ≈ (φ ∨ ψ) W ψ.
Lemma law_194 (φ ψ : LTL) : φ W ψ ≈ □ (φ ∧ ¬ ψ) ∨ (φ U ψ).
Lemma law_195 (φ ψ : LTL) : φ U ψ ≈ (φ W ψ) ∧ ◇ ψ.
Lemma law_196 (φ ψ : LTL) : φ U ψ ≈ (φ W ψ) ∧ ¬□¬ ψ.
Lemma law_197 (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Lemma law_198 (φ ψ : LTL) : φ W ψ ≈ ψ ∨ (φ ∧ ◯ (φ W ψ)).
Lemma law_199 (φ ψ : LTL) : φ W ψ ≈ (φ ∧ ¬ ψ) W ψ.
Lemma law_200 (φ ψ : LTL) : φ W (φ W ψ) ≈ φ W ψ.
Lemma law_201 (φ ψ : LTL) : (φ W ψ) W ψ ≈ φ W ψ.
Lemma law_202 (φ ψ : LTL) : φ W (φ U ψ) ≈ φ W ψ.
Lemma law_203 (φ ψ : LTL) : (φ U ψ) W ψ ≈ φ U ψ.
Lemma law_204 (φ ψ : LTL) : φ U (φ W ψ) ≈ φ W ψ.
Lemma law_205 (φ ψ : LTL) : (φ W ψ) U ψ ≈ φ U ψ.
Lemma law_206 (φ ψ : LTL) : ◯ (φ W ψ) ≈ ◯ φ W ◯ ψ.
Lemma law_207 (φ ψ : LTL) : φ W ◇ ψ ≈ □ φ ∨ ◇ ψ.
Lemma law_208 (φ : LTL) : ◇ φ W φ ≈ ◇ φ.
Lemma law_209 (φ ψ : LTL) : □ φ ∧ (φ W ψ) ≈ □ φ.
Lemma law_210 (φ ψ : LTL) : □ φ ∨ (φ W ψ) ≈ φ W ψ.
Lemma law_211 (φ : LTL) : φ W □ φ ≈ □ φ.
Lemma law_212 (φ : LTL) : □ φ ≈ φ W ⊥.
Lemma law_213 (φ : LTL) : ◇ φ ≈ ¬(¬ φ W ⊥).
Lemma law_214 (φ : LTL) : ⊤ W φ ≈ ⊤.
Lemma law_215 (φ : LTL) : φ W (⊤) ≈ ⊤.
Lemma law_216 (φ : LTL) : ⊥ W φ ≈ φ.
Lemma law_217 (φ ψ χ : LTL) : φ W (ψ ∨ χ) ≈ (φ W ψ) ∨ (φ W χ).
Lemma law_218 (φ ψ χ : LTL) : (φ ∧ ψ) W χ ≈ (φ W χ) ∧ (ψ W χ).
Lemma law_219 (φ ψ : LTL) : φ ∨ (φ W ψ) ≈ φ ∨ ψ.
Lemma law_220 (φ ψ : LTL) : (φ W ψ) ∨ ψ ≈ φ W ψ.
Lemma law_221 (φ ψ : LTL) : (φ W ψ) ∧ ψ ≈ ψ.
Lemma law_222 (φ ψ : LTL) : (φ W ψ) ∧ (φ ∨ ψ) ≈ φ W ψ.
Lemma law_223 (φ ψ : LTL) : (φ W ψ) ∨ (φ ∧ ψ) ≈ φ W ψ.
Lemma law_224 (φ ψ : LTL) : ((¬ φ U ψ) ∨ (¬ ψ U φ)) ≈ ◇ (φ ∨ ψ).
Lemma law_225 (φ ψ : LTL) : forall s, ψ s -> (φ W ψ) s.
Lemma law_226 (φ ψ : LTL) : forall s, (φ W φ) s -> (φ ∨ ψ) s.
Lemma law_227 (φ ψ : LTL) : forall s, (φ W φ) s -> (□ φ ∨ ◇ ψ) s.
Lemma law_228 (φ : LTL) : forall s, (¬ φ W φ) s.
Lemma law_229 (φ ψ : LTL) : forall s, ((φ → ψ) W φ) s.
Lemma law_230 (φ ψ : LTL) : forall s, ((φ W ψ) ∨ (φ W ¬ ψ)) s.
Lemma law_231 (φ ψ χ : LTL) : forall s, (φ W (ψ ∧ χ)) s -> ((φ W ψ) ∧ (φ W χ)) s.
Lemma law_232 (φ ψ χ : LTL) : forall s, ((φ W χ) ∨ (ψ W χ)) s -> ((φ ∨ ψ) W χ) s.
Lemma law_233 (φ ψ : LTL) : forall s, (φ U ψ) s -> (φ W ψ) s.
Lemma law_234 (φ ψ : LTL) : forall s, (φ W □ ψ) s -> □ (φ W ψ) s.
Lemma law_235 (φ ψ : LTL) : forall s, ¬(φ U ψ) s -> ((φ ∧ ¬ ψ) W (¬ φ ∧ ¬ ψ)) s.
Lemma law_236 (φ ψ : LTL) : forall s, ¬(φ W ψ) s -> ((φ ∧ ¬ ψ) U (¬ φ ∧ ¬ ψ)) s.
Lemma law_237 (φ ψ χ : LTL) : forall s, ((φ → ψ) W χ) s -> ((φ W χ) → (ψ W χ)) s.
Lemma law_238 (φ ψ : LTL) : forall s, □ φ s -> (φ W ψ) s.
Lemma law_239 (φ ψ : LTL) : forall s, □ φ s -> (◯ ψ → ◯ (φ W ψ)) s.
Lemma law_240 (φ ψ : LTL) : forall s, □ φ s -> (◇ ψ → ◇ (φ W ψ)) s.
Lemma law_241 (φ ψ : LTL) : forall s, □ φ s -> (□ ψ → □ (φ W ψ)) s.
Lemma law_242 (φ ψ : LTL) : forall s, □ (φ ∨ ψ) s -> (φ W ψ) s.
Lemma law_243 (φ ψ : LTL) : forall s, □ (¬ ψ → φ) s -> (φ W ψ) s.
Lemma law_244 (φ ψ χ : LTL) : forall s, □ (φ → (◯ φ ∧ ψ) ∨ χ) s -> (φ → ψ W χ) s.
Lemma law_245 (φ ψ : LTL) : forall s, □ (φ → ◯ (φ ∨ ψ)) s -> (φ → φ W ψ) s.
Lemma law_246 (φ ψ : LTL) : forall s, □ (φ → ◯ φ) s -> (φ → φ W ψ) s.
Lemma law_247 (φ ψ : LTL) : forall s, □ (φ → ψ ∧ ◯ φ) s -> (φ → φ W ψ) s.
Lemma law_248 (φ ψ χ : LTL) : forall s, (□ φ ∧ (ψ W χ)) s -> ((φ ∧ ψ) W (φ ∧ χ)) s.
Lemma law_249 (φ ψ : LTL) : forall s, ((φ W ψ) ∧ □¬ ψ) s -> □ φ s.
Lemma law_250 (φ ψ : LTL) : forall s, □ φ s -> ((φ U ψ) ∨ □¬ ψ) s.
Lemma law_251 (φ ψ : LTL) : forall s, (¬□ φ ∧ (φ W ψ)) s -> ◇ ψ s.
Lemma law_252 (φ ψ : LTL) : forall s, ◇ ψ s -> (¬□ φ ∨ (φ U ψ)) s.
Lemma law_253 (φ ψ χ : LTL) : forall s, □ (φ → ψ) s -> (φ W χ → ψ W χ) s.
Lemma law_254 (φ ψ χ : LTL) : forall s, □ (φ → ψ) s -> (χ W φ → χ W ψ) s.
Lemma law_255 (φ ψ χ ρ : LTL) : forall s, □ ((φ → χ) ∧ (ψ → ρ)) s -> ((φ W ψ) → (χ W ρ)) s.
Lemma law_256 (φ ψ χ ρ : LTL) : forall s, □ ((φ → ψ W χ) ∧ (χ → ψ W ρ)) s -> (φ → ψ W ρ) s.
Lemma law_257 (φ ψ χ : LTL) : forall s, ((φ U ψ) W χ) s -> ((φ W ψ) W χ) s.
Lemma law_258 (φ ψ χ : LTL) : forall s, (φ W (ψ U χ)) s -> (φ W (ψ W χ)) s.
Lemma law_259 (φ ψ χ : LTL) : forall s, (φ U (ψ U χ)) s -> (φ U (ψ W χ)) s.
Lemma law_260 (φ ψ χ : LTL) : forall s, ((φ U ψ) U χ) s -> ((φ W ψ) U χ) s.
Lemma law_261 (φ ψ χ : LTL) : forall s, ((φ U ψ) U χ) s -> ((φ ∨ ψ) U χ) s.
Lemma law_262 (φ ψ χ : LTL) : forall s, ((φ W ψ) W χ) s -> ((φ ∨ ψ) W χ) s.
Lemma law_263 (φ ψ χ : LTL) : forall s, (φ W (ψ W χ)) s -> (φ W (ψ ∨ χ)) s.
Lemma law_264 (φ ψ χ : LTL) : forall s, (φ W (ψ W χ)) s -> ((φ ∨ ψ) W χ) s.
Lemma law_265 (φ ψ χ : LTL) : forall s, (φ W (ψ ∧ χ)) s -> ((φ W ψ) W χ) s.
Lemma law_266 (φ ψ : LTL) : forall s, ((¬ φ W ψ) ∨ (¬ ψ W φ)) s.
Lemma law_267 (φ ψ χ : LTL) : forall s, ((φ W ψ) ∧ (¬ ψ W χ)) s -> (φ W χ) s.

Lemma law_268 (φ ψ : LTL) : φ R ψ ≈ ¬(¬ φ U ¬ ψ).
Lemma law_269 (φ ψ : LTL) : φ U ψ ≈ ¬(¬ φ R ¬ ψ).
Lemma law_270 (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Lemma law_271 (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Lemma law_272 (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ ◯ (φ R ψ)).
Lemma law_273 (φ ψ χ : LTL) : φ R (ψ ∨ χ) ≈ (φ R ψ) ∨ (φ R χ). (* ??? *)
Lemma law_274 (φ ψ χ : LTL) : (φ ∧ ψ) R χ ≈ (φ R χ) ∧ (ψ R χ). (* ??? *)
Lemma law_275 (φ ψ : LTL) : ◯ (φ R ψ) ≈ (◯ φ) R (◯ ψ).
Lemma law_276 (φ ψ : LTL) : □ ψ ≈ ⊥ R ψ.

Lemma law_277 (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Lemma law_278 (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Lemma law_279 (φ ψ : LTL) : ¬(φ W ψ) ≈ (¬ φ M ¬ ψ).
Lemma law_280 (φ ψ : LTL) : ¬(φ M ψ) ≈ (¬ φ W ¬ ψ).

(** Principles of negation *)

Lemma not_next (φ : LTL) : ¬(◯ φ) ≈ ◯ ¬φ.
Proof. split; repeat intro; auto. Qed.

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
Lemma always_not_eventually (ψ : LTL) : □ ψ ≈ ¬◇ ¬ψ.
Lemma release_until (φ ψ : LTL) : φ R ψ ≈ ¬(¬φ U ¬ψ).
Lemma weakUntil_release_or (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Lemma release_weakUntil_and (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Lemma weakUntil_until_or (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Lemma strongRelease_not_weakUntil (φ ψ : LTL) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Lemma strongRelease_and_release (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Lemma strongRelease_release_and (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).

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
Lemma asborb_always (φ : LTL) : □ ◇ □ φ ≈ ◇ □ φ.

(** Predicates on elements *)

Definition examine (P : a -> LTL) : LTL := fun s => P (head s) s.

Inductive release (p q : LTL) : LTL :=
  | release_hd s : q s -> p s -> release p q s
  | release_tl x s : q (Cons x s) -> release p q s -> release p q (Cons x s).

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
