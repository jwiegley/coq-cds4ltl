Set Warnings "-local-declaration".

Require Import
  Coq.Unicode.Utf8
  Coq.Program.Program
  Coq.micromega.Lia
  Coq.Classes.Morphisms
  Coq.Setoids.Setoid
  MinLTL
  LTL.

(** PLTL *)
Module Type PastTimeLinearTemporalLogic <: LinearTemporalLogic.

Include LinearTemporalLogic.

Parameter previous : t -> t.
Parameter since : t -> t -> t.

Notation "◯⁻¹ p"   := (previous p) (at level 75, right associativity) : ltl_scope.
Notation "p 'S' q" := (since p q)  (at level 79, right associativity) : ltl_scope.

End PastTimeLinearTemporalLogic.

(** LTLf *)
Module Type FiniteLinearTemporalLogic <: LinearTemporalLogic.

Include LinearTemporalLogic.

Parameter fin : t.
Parameter weak_next : t.

Notation "● p" := (weak_next p) (at level 75, right associativity) : ltl_scope.
Notation "∎"   := fin           (at level 79, right associativity) : ltl_scope.

End FiniteLinearTemporalLogic.

(** CTL *)
Module Type ComputationTreeLogic <: LinearTemporalLogic.

Include LinearTemporalLogic.

Parameter exist_next : t -> t.
Parameter exist_always : t -> t.
Parameter exist_until : t -> t -> t.

End ComputationTreeLogic.

(** CTL* *)
Module Type FullBranchingTimeLogic <: LinearTemporalLogic.

Include LinearTemporalLogic.

Parameter s : Type.

End FullBranchingTimeLogic.

(** LDL *)
Module Type LinearDynamicLogic <: LinearTemporalLogic.

Include LinearTemporalLogic.

Parameter regular  : t -> t -> t.
Parameter query    : t -> t.
Parameter select   : t -> t -> t.
Parameter sequence : t -> t -> t.
Parameter kleene   : t -> t.

Notation "⟨ p ⟩ q" := (regular p q)  (at level 75, right associativity) : ltl_scope.
Notation "p ?"     := (query p)      (at level 75, right associativity) : ltl_scope.
Notation "p + q"   := (select p q)   (at level 50, left associativity) : ltl_scope.
Notation "p ; q"   := (sequence p q) (at level 75, right associativity) : ltl_scope.
Notation "p *"     := (kleene p)     (at level 75, right associativity) : ltl_scope.

End LinearDynamicLogic.

Module Type EpistemicLinearTemporalLogic <: LinearTemporalLogic.

Include LinearTemporalLogic.

End EpistemicLinearTemporalLogic.
