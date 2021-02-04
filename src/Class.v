Require Import
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.SetoidClass.

Notation "f ≈ g" := equiv (at level 79).
Reserved Notation "¬ p"   (at level 0).
Reserved Infix    "∨"     (at level 46, right associativity).
Reserved Notation "⊤"     (at level 0).
Reserved Notation "⊥"     (at level 0).

Class MinimalBooleanLogic {t : Type} := {
  is_setoid :> Setoid t;

  not   : t -> t      where "¬ p"   := (not p);
  or    : t -> t -> t where "p ∨ q" := (or p q);
  true  : t           where "⊤"     := (true);
  false : t           where "⊥"     := (false);

  not_respects : Proper (equiv ==> equiv) not;
  or_respects  : Proper (equiv ==> equiv ==> equiv) or;

  true_def  {φ : t} : ⊤ ≈ φ ∨ ¬ φ;
  false_def {φ : t} : ⊥ ≈ ¬ (φ ∨ ¬ φ);

  or_true      {φ     : t} : φ ∨ ⊤ ≈ ⊤;
  or_false     {φ     : t} : φ ∨ ⊥ ≈ φ;
  or_comm      {φ ψ   : t} : φ ∨ ψ ≈ ψ ∨ φ;
  or_assoc     {φ ψ χ : t} : (φ ∨ ψ) ∨ χ ≈ φ ∨ (ψ ∨ χ);
  or_distr_not {φ ψ χ : t} : ¬ (¬ (φ ∨ ψ) ∨ ¬ (φ ∨ χ)) ≈ φ ∨ ¬ (¬ ψ ∨ ¬ χ);
}.
