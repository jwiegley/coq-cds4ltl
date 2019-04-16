Require Import FunInd.
Require Import Program.

Section Foo.

Variable a : Type.

Inductive Higher :=
  | Ctor (f : a -> Higher)
  | Neg (x : Higher)
  | Rec (x : Higher).

Function foo (h : Higher) : Higher :=
  match h with
  | Ctor f => Ctor (foo ∘ f)
  | Neg x => Rec (bar x)
  | Rec x => Rec (foo x)
  end
with
  bar (h : Higher) : Higher :=
  match h with
  | Ctor f => Ctor (bar ∘ f)
  | Neg x => Rec (foo x)
  | Rec x => Rec (bar x)
  end.

(* foo is defined
   bar is defined
   foo, bar are recursively defined (decreasing respectively on 1st,
   1st arguments)
   foo_equation is defined
   foo_ind is defined
   foo_rec is defined
   foo_rect is defined
   bar_equation is defined
   bar_ind is defined
   bar_rec is defined
   bar_rect is defined
   R_foo_correct is defined
   R_bar_correct is defined
   R_foo_complete is defined
   R_bar_complete is defined *)

(** Note the induction hypothesis for Ctor:

    (forall f : a -> Higher, (forall a : a, P (f a)) -> P (Ctor f)) *)

Print Higher_ind.

(** It is missing for foo_ind:

    (forall (h : Higher) (f : a -> Higher),
      h = Ctor f -> P (Ctor f) (Ctor (foo ∘ f))) *)

Print foo_ind.

Functional Scheme foo_ind2 := Induction for foo Sort Prop
  with bar_ind2 := Induction for bar Sort Prop.

(** And also for foo_ind2:

    (forall (h : Higher) (f : a -> Higher),
        h = Ctor f -> P (Ctor f) (Ctor (foo ∘ f)))
    (forall (h : Higher) (f2 : a -> Higher),
        h = Ctor f2 -> P0 (Ctor f2) (Ctor (bar ∘ f2))) *)

Print foo_ind2.

Function foo' (h : Higher) : Higher :=
  match h with
  | Ctor f => Ctor (fun x => foo' (f x))
  | Neg x => Rec (bar' x)
  | Rec x => Rec (foo' x)
  end
with
  bar' (h : Higher) : Higher :=
  match h with
  | Ctor f => Ctor (fun x => bar' (f x))
  | Neg x => Rec (foo' x)
  | Rec x => Rec (bar' x)
  end.

(** Why does it now fail to build the graph?

    foo' is defined
    bar' is defined
    foo', bar' are recursively defined (decreasing respectively on 1st,
    1st arguments)
    Warning: Cannot define graph(s) for foo', bar'
    [funind-cannot-define-graph,funind]
    Warning: Cannot build inversion information
    [funind-cannot-build-inversion,funind] *)

End Foo.
