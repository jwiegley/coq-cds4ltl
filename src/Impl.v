Require Import
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Program.Program.

Module Type Implication.

Parameter t : Type.

Parameter impl : t -> t -> Prop.
Parameter equiv : t -> t -> Prop.

(* Infix "⟹" := impl  (at level 91). *)
Infix "≈"  := equiv (at level 90).

(* Hypothesis equiv_def : forall (φ ψ : t), φ ≈ ψ <-> (φ ⟹ ψ) /\ (ψ ⟹ φ). *)

Declare Instance impl_reflexive : Reflexive impl.
Declare Instance impl_transitive : Transitive impl.
Declare Instance equiv_equivalence : Equivalence equiv.

Declare Instance impl_equiv : Proper (equiv ==> equiv ==> Basics.impl) impl.

Global Program Instance equiv_equiv :
  Proper (equiv ==> equiv ==> Basics.impl) equiv.
Next Obligation.
  repeat intro.
  now rewrite <- H, <- H0.
Qed.

Global Program Instance equiv_flip_equiv :
  Proper (equiv ==> equiv ==> flip Basics.impl) equiv.
Next Obligation.
  repeat intro.
  now rewrite H, H0.
Qed.

Global Program Instance equiv_iff :
  Proper (equiv ==> equiv ==> iff) equiv.
Next Obligation.
  repeat intro.
  split; intro.
  - rewrite <- H.
    now rewrite H1.
  - rewrite H.
    now rewrite H0.
Qed.

(*
Goal forall (f : t -> t) (x y : t),
  Proper (impl ==> impl) f
    -> x ⟹ y
    -> f x ⟹ f y.
Proof.
  intros.
  rewrite H0.
  rewrite <- H0 at 2.           (* otherwise it tries "at 1" *)
Abort.
*)

End Implication.
