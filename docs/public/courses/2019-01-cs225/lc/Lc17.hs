module Lc17 where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.List          -- used in testing infrastructure
import Control.Monad      -- used in testing infrastructure
import Control.Exception  -- used in testing infrastructure
import System.IO          -- used in testing infrastructure

import qualified Debug.Trace as Debug

-- x ∈ var ≈ symbol
-- e ⩴ i
--   | e + e
--   | b
--   | IF e THEN e ELSE e
data Expr = IntE Integer
          | PlusE Expr Expr
          | BoolE Bool
          | IfE Expr Expr Expr
  deriving (Eq,Ord,Show)

-- v ∈ value ⩴ i
--           | b
data Value = IntV Integer
           | BoolV Bool
  deriving (Eq,Ord,Show)

-- τ ∈ type ⩴ int
--          | bool
data Type = IntT 
          | BoolT 
  deriving (Eq,Ord,Show)

check :: Expr -> Maybe Type
check e0 = case e0 of
  IntE i -> Just IntT 
         -- Just (IntV i)
  PlusE e1 e2 -> 
      case (check e1, check e2) of
        (Just IntT, Just IntT) -> Just IntT
        _ -> Nothing
   -- case (interp e1, interp e2) of
   --   (Just (IntV i1), Just (IntV i2)) -> Just (IntV (i1 + i2))
   --   _ -> Nothing
  BoolE b -> Just BoolT 
          -- Just (BoolV b)
  IfE e1 e2 e3 -> 
       case check e1 of
         Just BoolT -> case (check e2, check e3) of
           (Just t2, Just t3) -> if t2 == t3 then Just t2 else Nothing
           _ -> Nothing
         _ -> Nothing
    -- case interp e1 of
    --   Just (BoolV b) -> 
    --     if b 
    --     then interp e2 
    --     else interp e2
    --   _ -> Nothing
