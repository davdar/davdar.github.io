{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Lc08 where

import Data.Char

import Data.Set (Set)
import qualified Data.Set as Set

-- useful functions from the Data.Set module
--
-- Set a ≈ ℘(a)
--
-- Set.empty     :: Set a                       
-- Set.singleton :: a -> Set a                  
-- Set.fromList  :: [a] -> Set a                
--
-- Set.empty            ≈ ∅
-- Set.singleton x      ≈ {x}
-- Set.fromList [x,y,z] ≈ {x,y,z}
--
-- Set.union        :: Set a -> Set a -> Set a         
-- Set.intersection :: Set a -> Set a -> Set a
-- Set.difference   :: Set a -> Set a -> Set a
--
-- Set.union xs ys        ≈ xs ∪ ys
-- Set.intersection xs ys ≈ xs ∩ ys
-- Set.difference xs ys   ≈ xs ∖ ys
--
-- Set.member     :: a -> Set a -> Bool
-- Set.isSubsetOf :: Set a -> Set a -> Bool
--
-- Set.member x xs      ≈ x ∈ xs
-- Set.isSubsetOf xs ys ≈ xs ⊆ ys
--
-- full API here: 
--
--     http://hackage.haskell.org/package/containers-0.6.0.1/docs/Data-Set.html  

import Data.Map (Map)
import qualified Data.Map as Map

-- useful functions from the Data.Map module
--
-- Map k v ≈ k ⇰ v ≈ {R ∈ ℘(k × v) | R is functional}
--
-- Map.empty     :: Map k v
-- Map.singleton :: k -> v -> Map k v
-- Map.fromList  :: [(k,v)] -> Map k v
--
-- Map.empty                              ≈ ∅ 
-- Map.singleton k v                      ≈ {k ↦ v}
-- Map.fromList [(k₁,v₁),(k₂,v₂),(k₃,v₃)] ≈ {k₁ ↦ v₁,k₂ ↦ v₂,k₃ ↦ v₃}
--
-- Map.union :: Map k v -> Map k v -> Map k v
-- Map.intersection :: Map k v -> Map k v -> Map k v
-- Map.difference :: Map k v -> Map k v -> Map k v
--
-- Map.union kvs₁ kvs₂        ≈ kvs₁ ∪ kvs₂
-- Map.intersection kvs₁ kvs₂ ≈ kvs₁ ∩ kvs₂
-- Map.difference kvs₁ kvs₂   ≈ kvs₁ ∖ kvs₂
--
-- Map.member     :: k -> Map k v -> Bool
-- Map.lookup     :: k -> Map k v -> Maybe v
-- Map.isSubmapOf :: Map k v -> Map k v -> Bool
--
-- full API here:
-- 
--     http://hackage.haskell.org/package/containers-0.6.0.1/docs/Data-Map-Lazy.html

-- Let's get to know the maybe type...
--
data Maybe' a = 
    Nothing' 
  | Just' a

-- there are two types of *values* of type `Maybe a`
--
-- Nothing :: Maybe a 
--
-- if 
--   v :: a
-- then
--   Just v :: Maybe a
--
-- when *creating* a `Maybe a` value, you have two options:
-- 1. create a `Nothing`
-- 2. create a `Just _` with something of type `a` in the hole
--
-- when *using* a `Maybe a` value, you *must* do a case analysis, and handle
-- two cases:
-- 1. handle the case that it was a `Nothing`
-- 2. handle the case that it was a `Just _`
--
-- `Maybe a` is an encoding of the idea of a "nullable value". You either have
-- NULL (the `Nothing` case) or you have a value of type `a` which is not NULL
-- (the `Just` case)

maybeToList :: Maybe Integer -> [Integer]
maybeToList iM = case iM of
  Nothing -> []
  Just i -> [i]

maybeToList' :: Maybe Integer -> [Integer]
maybeToList' Nothing = []
maybeToList' (Just i) = [i]

listHead :: [Integer] -> Maybe Integer
listHead [] = Nothing
listHead (x:xs) = Just x

listTail :: [Integer] -> Maybe [Integer]
listTail [] = Nothing
listTail (x:xs) = Just xs

listUncons :: [Integer] -> Maybe (Integer,[Integer])
listUncons [] = Nothing
listUncons (x:xs) = Just (x,xs)

listUnsnoc :: [Integer] -> Maybe ([Integer],Integer)
listUnsnoc [] = Nothing
listUnsnoc (x:xs) = case listUnsnoc xs of
  Nothing -> Just ([],x)
  Just (xs',x') -> Just (x:xs',x')

reverseUnsnoc :: [Integer] -> [Integer]
reverseUnsnoc xs = case listUnsnoc xs of
  Nothing -> []
  Just (xs',x) -> x : reverseUnsnoc xs'

lookup2 :: Integer -> Map Integer Char -> Map Char Double -> Maybe Double
lookup2 x kvs1 kvs2 = case Map.lookup x kvs1 of
  Nothing -> Nothing
  Just y -> case Map.lookup y kvs2 of
    Nothing -> Nothing
    Just z -> Just z

