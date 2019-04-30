Require Import
  Program
  Coq.Lists.List
  Coq.Relations.Relation_Definitions
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Logic.Classical
  Coq.Sets.Ensembles
  Hask.Control.Monad
  Hask.Prelude.

Open Scope program_scope.
Open Scope list_scope.

Require Import LTL.
Require Import Step.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Section Machine.

Variable a : Type.              (* The type of entries in the trace *)

Inductive Machine (a b : Type) : Type :=
  Mach : (a -> Machine a b + b) -> Machine a b.

(*
instance Functor (Machine a) where
  fmap f (Machine k) = Machine $ either (Left . fmap f) (Right . f) . k
*)

(* Definition run : Machine a b -> list a -> Machine a b + b := *)
(*   fold_left (either step (const . Right)) . Left *)

data Reason a
  = HitBottom   String
  | Rejected    a
  | BothFailed  (Reason a) (Reason a)
  | LeftFailed  (Reason a)
  | RightFailed (Reason a)
  deriving (Show, Generic, NFData, Functor)

type Result a = Maybe (Reason a)

type LTL a = Machine a (Result a)

stop :: Result a -> LTL a
stop = Machine . const . Right

top :: LTL a
top = stop Nothing

bottom :: String -> LTL a
bottom = stop . Just . HitBottom

neg :: LTL a -> LTL a
neg = fmap invert

and :: LTL a -> LTL a -> LTL a
and (Machine f) g = Machine $ \a -> case f a of
  Right (Just e) -> Right (Just (LeftFailed e))
  Right Nothing  -> step g a
  Left f'        -> case step g a of
    Right (Just e) -> Right (Just (RightFailed e))
    Right Nothing  -> Left f'
    Left g'        -> Left $! f' `and` g'

andNext :: LTL a -> LTL a -> LTL a
andNext (Machine f) g = Machine $ \a -> case f a of
  Right (Just e) -> Right (Just (LeftFailed e))
  Right Nothing  -> Left g
  Left f'        -> Left $! f' `and` g

or :: LTL a -> LTL a -> LTL a
or (Machine f) g = Machine $ \a -> case f a of
  Right Nothing   -> Right Nothing
  Right (Just e1) -> case step g a of
    Right (Just e2) -> Right (Just (BothFailed e1 e2))
    g'              -> g'
  Left f' -> case step g a of
    Right Nothing  -> Right Nothing
    Right (Just _) -> Left f'
    Left g'        -> Left $! f' `or` g'

orNext :: LTL a -> LTL a -> LTL a
orNext (Machine f) g = Machine $ \a -> case f a of
  Right Nothing  -> Right Nothing
  Right (Just _) -> Left g
  Left f'        -> Left $! f' `or` g

invert :: Result a -> Result a
invert = \case
  Nothing -> Just (HitBottom "neg")
  Just _  -> Nothing

accept :: (a -> LTL a) -> LTL a
accept f = Machine $ \a -> step (f a) a

reject :: (a -> LTL a) -> LTL a
reject = neg . accept

next :: LTL a -> LTL a
next = Machine . const . Left

until :: LTL a -> LTL a -> LTL a
until p = \q -> fix $ or q . andNext p

weakUntil :: LTL a -> LTL a -> LTL a
weakUntil p = \q -> (p `until` q) `or` always p

release :: LTL a -> LTL a -> LTL a
release p = \q -> fix $ and q . orNext p

strongRelease :: LTL a -> LTL a -> LTL a
strongRelease p = \q -> (p `release` q) `and` eventually p

implies :: LTL a -> LTL a -> LTL a
implies = or . neg

eventually :: LTL a -> LTL a
eventually = until top

always :: LTL a -> LTL a
always = release (bottom "always")

truth :: Bool -> LTL a
truth True  = top
truth False = bottom "truth"

is :: (a -> Bool) -> LTL a
is = accept . (truth .)

test :: (a -> Bool) -> LTL a
test = is

eq :: Eq a => a -> LTL a
eq = is . (==)

showResult :: Show a => Either (LTL a) (Result a) -> String
showResult (Left _)  = "<need input>"
showResult (Right b) = show b

