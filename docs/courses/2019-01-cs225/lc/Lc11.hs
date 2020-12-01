{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Lc11 where

import Data.Char

import Data.Set (Set)
import qualified Data.Set as Set

-- let's learn about higher order functions, filter and map.

-- we write multi-argument functions with arrows between the arguments in
-- Haskell

plus :: Integer -> Integer -> Integer
plus x y = x + y

-- the implicit parens are placed in the definition are like so

plus' :: Integer -> (Integer -> Integer)
plus' x y = x + y

-- functions can be "partially applied", you give it the first argument, and it
-- returns a function which expects the second argument

plusFive :: Integer -> Integer
plusFive = plus 5

-- functions can also be written in "anonymous function" form

plusFive' :: Integer -> Integer
plusFive' = \ y -> 5 + y
--          ^ ^    ^^^^^
--          | |    function body
--          | |
--  "lambda"   the parameter

plusOfSquares :: Integer -> Integer -> Integer
plusOfSquares x =
--                
  let xx = x * x in
--           reference to outside variable
--           ⌄⌄
      \ y -> xx + y * y
--    ^ ^    ^^^^^^^^^^
--    | |    function body
--    | |
-- "lambda"   the parameter

-- let's look at the type of filter
-- filter :: (a -> Bool) -> [a] -> [a]
--
-- filter takes a predicate `p : a -> Bool` and keeps elements of the list for
-- which the predicate returns true

isEven :: Integer -> Bool
isEven i = (i `mod` 2) == 0

onlyEvens :: [Integer] -> [Integer]
onlyEvens is = filter isEven is

onlyEvens' :: [Integer] -> [Integer]
onlyEvens' is = filter (\ i -> (i `mod` 2) == 0) is

onlyEvens'' :: [Integer] -> [Integer]
onlyEvens'' = filter (\ i -> (i `mod` 2) == 0)

onlyMultiples :: Integer -> [Integer] -> [Integer]
onlyMultiples i = filter (\ j -> (j `mod` i) == 0)

-- let's take a look at the type of map
-- map :: (a -> b) -> [a] -> [b]
--
-- map takes a function which transforms `a` things into `b` things, and
-- applies this to every element of a list

upperCaseString :: [Char] -> [Char]
upperCaseString [] = []
upperCaseString (c:cs) = toUpper c : upperCaseString cs

upperCaseString' :: [Char] -> [Char]
upperCaseString' cs = map (\ c -> toUpper c) cs

upperCaseString'' :: [Char] -> [Char]
upperCaseString'' = map (\ c -> toUpper c)

upperCaseString''' :: [Char] -> [Char]
upperCaseString''' = map toUpper
