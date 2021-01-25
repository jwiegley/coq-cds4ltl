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
