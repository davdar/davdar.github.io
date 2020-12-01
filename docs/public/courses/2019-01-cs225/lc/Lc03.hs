-- Lecture Code Notes
module Lc03 where

-- Our first definition of a programming language syntax in Haskell:

--     e ∈ expr ⩴ i
--              | e + e
--              | e × e
--
data Expr = IntE Integer     -- note: *not* `Int`
          | PlusE Expr Expr 
          | TimesE Expr Expr
  deriving (Eq,Ord,Read,Show)

-- Template:
--
-- interp :: Expr -> …
-- interp e0 = case e0 of
--   IntE i -> _
--   PlusE e1 e2 -> … interp e1 … interp e2 …
--   TimesE e1 e2 -> … interp e1 … interp e2 …

-- Let's count the number of nodes in an expression
--
-- E.g.,
--
--     count-nodes (1 + 2 × 3 + 4) = 7
--
countNodes :: Expr -> Integer
countNodes e0 = case e0 of
  IntE i -> 1
  PlusE e1 e2 -> 1 + countNodes e1 + countNodes e2
  TimesE e1 e2 -> 1 + countNodes e1 + countNodes e2

-- Let's count the maximum depth of the syntax tree:
--
-- (Remember that + associates to the left, i.e., `1 + 2 + 3` is parsed as `(1
-- + 2) + 3`.)
--
-- E.g.,
--
--     max-depth (1 + 2 × 3 × 4 + 5) = 4
--
maxDepth :: Expr -> Integer
maxDepth e0 = case e0 of
  IntE i -> 1
  PlusE e1 e2 -> 1 + (countNodes e1 `max` countNodes e2)
  TimesE e1 e2 -> 1 + (countNodes e1 `max` countNodes e2)

-- Let's swap the order of each of the operators:
--
-- E.g.,
--
--     swap-ops (1 + 2 × 3 × 4 + 5) = (5 + ((4 × (3 × 2)) + 1))
--
swapOps :: Expr -> Expr
swapOps e0 = case e0 of
  IntE i -> IntE i
  PlusE e1 e2 -> PlusE e2 e1
  TimesE e1 e2 -> TimesE e2 e1

-- Here is the interpreter for the language:
--
--     interp (1 + 2 × 3 + 4) = 11
--
interp :: Expr -> Integer
interp e0 = case e0 of
  IntE i -> i
  PlusE e1 e2 -> interp e1 + interp e2
  TimesE e1 e2 -> interp e1 * interp e2
