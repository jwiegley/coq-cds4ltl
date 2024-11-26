Set Warnings "-local-declaration".

Require Import
  Coq.Unicode.Utf8
  Coq.Program.Program
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid
  Bool.

(***********************************************************************
 * This axiomatization of Linear Temporal Logic follows directly from
 * the paper:
 *
 * "A Calculational Deductive System for Linear Temporal Logic"
 * https://dl.acm.org/doi/10.1145/3387109
 *
 * by Warford, Vega and Staley *)

Module Type ScheinderAxioms <: BooleanLogic.

Include BooleanLogic.

Parameter always     : t -> t.
Parameter eventually : t -> t.
Parameter next       : t -> t.
Parameter wait       : t -> t -> t.

#[global]
Declare Scope ltl_scope.
Bind Scope ltl_scope with t.
Delimit Scope ltl_scope with ltl.
Open Scope boolean_scope.
Open Scope ltl_scope.

Notation "□ p" := (always p) (at level 75, right associativity) : ltl_scope.
Notation "◇ p" := (eventually p) (at level 75, right associativity) : ltl_scope.
Notation "◯ p" := (next p) (at level 75, right associativity) : ltl_scope.
Notation "p 'W' q" := (wait p q) (at level 79, right associativity) : ltl_scope.

Axiom axiom_3_10a : ∀ p,   □ p ⟹ p.
Axiom axiom_3_10b : ∀ p q, □ (p ⇒ q) ⟹ (□ p ⇒ □ q).

Axiom axiom_3_15  : ∀ p,   ◇ p ≈ ¬□ ¬p.

Axiom axiom_3_21a : ∀ p,   ◯ ¬p ≈ ¬◯ p.
Axiom axiom_3_21b : ∀ p q, ◯ (p ⇒ q) ≈ ◯ p ⇒ ◯ q.
Axiom axiom_3_21c : ∀ p,   □ p ⟹ ◯ p.
Axiom axiom_3_21d : ∀ p,   □ p ⟹ ◯□ p.
Axiom axiom_3_21e : ∀ p,   □ (p ⇒ ◯ p) ⟹ (p ⇒ □ p).

Axiom axiom_3_27a : ∀ p q, □ p ⟹ p W q.
Axiom axiom_3_27b : ∀ p q, p W q ≈ q ∨ (p ∧ ◯ (p W q)).

End ScheinderAxioms.
