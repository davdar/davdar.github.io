-- Lecture Code Notes
module Lc06 where

import Data.Set (Set)
import qualified Data.Set as Set

-----------
-- Lists --
-----------

data Expr = IntE Integer
          | PlusE Expr Expr
          | TimesE Expr Expr
          | BoolE Bool
          | IfE Expr Expr Expr
          -- new things
          | VarE String
          | LetE String Expr Expr

-- v ∈ var ≜ string
-- S ∈ scope ≜ ℘(var)
--
-- S ⊢ e ∈ prop
wellFormed :: Set String -> Expr -> Bool
-- ─────
-- S ⊢ i
wellFormed scope (IntE i) = True
-- S ⊢ e₁
-- S ⊢ e₂
-- ───────────
-- S ⊢ e₁ + e₂
wellFormed scope (PlusE e1 e2) = wellFormed scope e1 && wellFormed scope e2
-- S ⊢ e₁
-- S ⊢ e₂
-- ───────────
-- S ⊢ e₁ × e₂
wellFormed scope (TimesE e1 e2) = wellFormed scope e1 && wellFormed scope e2
-- ─────
-- S ⊢ b
wellFormed scope (BoolE b) = True
-- S ⊢ e₁
-- S ⊢ e₂
-- S ⊢ e₃
-- ─────────────────────────
-- S ⊢ IF e₁ THEN e₂ ELSE e₃
wellFormed scope (IfE e1 e2 e3) = wellFormed scope e1 && wellFormed scope e2 && wellFormed scope e3
-- x ∈ S
-- ─────
-- S ⊢ x
wellFormed scope (VarE x) = x `Set.member` scope
-- S ⊢ e₁
-- {x}∪S ⊢ e₂
-- ────────────────────
-- S ⊢ LET x = e₁ IN e₂
wellFormed scope (LetE x e1 e2) = wellFormed scope e1 && wellFormed (Set.singleton x `Set.union` scope) e2

-- closed(e) ⟺  ∅ ⊢ e
closed :: Expr -> Bool
closed e = wellFormed Set.empty e

-- x
e1 :: Expr
e1 = VarE "x"

-- LET x = 1 IN x
e2 :: Expr
e2 = LetE "x" (IntE 1) (VarE "x")

-- LET x = 1 IN y
e3 :: Expr
e3 = LetE "x" (IntE 1) (VarE "y")

-- LET x = x IN x
e4 :: Expr
e4 = LetE "x" (VarE "x") (VarE "x")
