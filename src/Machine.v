Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.Classes.Morphisms
  Coq.Lists.List
  Syntax.

Open Scope program_scope.

CoInductive Machine (a b : Type) :=
  | Step : (a -> Machine a b + b) -> Machine a b.

Arguments Step {a b} _.

CoFixpoint map {a b c : Type} (f : b -> c) (p : Machine a b) : Machine a c :=
  match p with
  | Step k => Step (λ x, match k x with
                         | inl m => inl (map f m)
                         | inr r => inr (f r)
                         end)
  end.

Module LTLMachine (S : StreamType).

Module Import LTL := LTL S.

Inductive Failed : Type :=
  | HitBottom
  | Rejected    (x : S.a)
  | BothFailed  (p q : Failed)
  | LeftFailed  (p : Failed)
  | RightFailed (q : Failed).

Inductive Result : Type :=
  | Failure (e : Failed)
  | Success.

Definition LTL := Machine S.a Result.

Definition stop (r : Result) : LTL := Step (λ _, inr r).

Definition true := stop Success.

Definition false := stop (Failure HitBottom).

Definition invert (r : Result) : Result :=
  match r with
  | Failure e => Success
  | Success   => Failure HitBottom
  end.

Definition negate : LTL -> LTL := map invert.

Definition next (p : LTL) : LTL :=
  match p with
  | Step k => Step (λ _, inl (Step k))
  end.

CoFixpoint and (p q : LTL) : LTL :=
  match p with
  | Step k =>
    Step (λ a,
          match k a with
          | inr (Failure e) => inr (Failure (LeftFailed e))
          | inr Success     =>
            match q with
            | Step g => g a
            end
          | inl p' =>
            match q with
            | Step g =>
              match g a with
              | inr (Failure e) => inr (Failure (RightFailed e))
              | inr Success     => inl p'
              | inl q'          => inl (and p' q')
              end
            end
          end)
  end.

Definition andNext (p q : LTL) : LTL :=
  match p with
  | Step k =>
    Step (λ a,
          match k a with
          | inr (Failure e) => inr (Failure (LeftFailed e))
          | inr Success     => inl q
          | inl p'          => inl (and p' q)
          end)
  end.

CoFixpoint or (p q : LTL) : LTL :=
  match p with
  | Step k =>
    Step (λ a,
          match k a with
          | inr Success      => inr Success
          | inr (Failure e1) =>
            match q with
            | Step g =>
              match g a with
              | inr (Failure e2) => inr (Failure (BothFailed e1 e2))
              | q' => q'
              end
            end
          | inl p' =>
            match q with
            | Step g =>
              match g a with
              | inr Success     => inr Success
              | inr (Failure _) => inl p'
              | inl q'          => inl (or p' q')
              end
            end
          end)
  end.

Definition orNext (p q : LTL) : LTL :=
  match p with
  | Step k =>
    Step (λ a,
          match k a with
          | inr Success     => inr Success
          | inr (Failure _) => inl q
          | inl p'          => inl (or p' q)
          end)
  end.

(*
CoFixpoint until (p q : LTL) : LTL :=
  or q (andNext p (until p q)).

CoFixpoint wait (p q : LTL) : LTL :=
  or q (andNext p (wait p q)).

CoFixpoint always (p : LTL) : LTL :=
  andNext p (always p).

CoFixpoint eventually (p : LTL) : LTL :=
  orNext p (eventually p).

CoFixpoint release (p q : LTL) : LTL :=
  and q (orNext p (release p q)).

CoFixpoint strong_release (p q : LTL) : LTL :=
  and q (orNext p (strong_release p q)).
*)

End LTLMachine.
