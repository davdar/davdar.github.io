-- Lecture Code Live
module Lc04 where

import Data.Ratio -- support for rational numbers (type Rational)

-- e ∈ cexpr ⩴ i
--           | e + e
--           | e × e
data ExprC = IntEC Integer
           | PlusEC ExprC ExprC
           | TimesEC ExprC ExprC
  deriving (Eq,Ord,Read,Show)

-- eₛ ∈ sexpr ⩴ i
--            | e + e
--            | e × e
--            | e - e
--            | neg e
data ExprS = IntES Integer
           | PlusES ExprS ExprS
           | TimesES ExprS ExprS
           | MinusES ExprS ExprS
           | NegateES ExprS
  deriving (Eq,Ord,Read,Show)

interp :: ExprC -> Integer
interp (IntEC i) = i
interp (PlusEC e1 e2) = interp e1 + interp e2
interp (TimesEC e1 e2) = interp e1 * interp e2

desugar :: ExprS -> ExprC
desugar (IntES i) = IntEC i
desugar (PlusES e1 e2) = PlusEC (desugar e1) (desugar e2)
desugar (TimesES e1 e2) = TimesEC (desugar e1) (desugar e2)
desugar (MinusES e1 e2) = PlusEC (desugar e1) (TimesEC (IntEC (-1)) (desugar e2))
desugar (NegateES e) = TimesEC (IntEC (-1)) (desugar e)

-- e ∈ cexpr ⩴ i
--           | e + e
--           | e × e
--           | e / e
data ExprD = IntED Integer
           | PlusED ExprD ExprD
           | TimesED ExprD ExprD
           | DivideED ExprD ExprD
  deriving (Eq,Ord,Read,Show)

-- v ∈ value ⩴ q ∈ ℚ
type Value = Rational

-- a ∈ answer ⩴ v
--            | BAD
data Answer = ValA Value
            | BadA
  deriving (Eq,Ord,Read,Show)

interpD :: ExprD -> Answer
interpD (IntED i) = ValA (fromIntegral i)
interpD (PlusED e1 e2) = case (interpD e1,interpD e2) of
  (ValA q1,ValA q2) -> ValA (q1 + q2)
  _ -> BadA
interpD (TimesED e1 e2) = case (interpD e1,interpD e2) of
  (ValA q1,ValA q2) -> ValA (q1 * q2)
  _ -> BadA
interpD (DivideED e1 e2) = case (interpD e1,interpD e2) of
  (ValA q1,ValA q2) | q2 /= 0 -> ValA (q1 / q2)
  _ -> BadA
