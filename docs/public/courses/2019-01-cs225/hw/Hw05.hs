{-# LANGUAGE GADTs #-} -- used in testing infrastructure
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Hw05 where

{-

v1.2

Run this file with `stack runghc <this-file>`
Load this file into an interactive prompt with `stack ghci <this-file>`

Name: <put your name here>

Collaboration Statement:

<put your collaboration statement here>

Course Policy Reminder:

    Collaboration with peers on the high-level ideas and approach on
    assignments is encouraged. Copying someone else's work is not allowed. Any
    collaboration, even at a high level, must be declared when you submit your
    assignment. Every assignment must include a collaboration statement. E.g.,
    “I discussed high-level strategies for solving problem 2 and 5 with Alex.”

    Obtaining high-level information on the internet is allowed and encouraged
    if it helps you learn the material. However, I strongly discourage googling
    for answers to homework problems. Copying code from the internet and
    submitting copied content for assignments is not allowed.

    Students caught copying work from peers or submitting copied code from the
    internet will be eligible for immediate failure of the course and
    disciplinary action by the University. All academic integrity misconduct
    will be treated according to UVM's Code of Academic Integrity.

-}

import Data.List          -- used in testing infrastructure
import Control.Monad      -- used in testing infrastructure
import Control.Exception  -- used in testing infrastructure
import System.IO          -- used in testing infrastructure

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

---------------------
-- LANGUAGE SYNTAX --
---------------------

-- i ∈ ℤ ≜ {…,-2,-1,0,1,2,…}
-- b ∈ 𝔹 ≜ {true,false}
-- x ∈ var      ≜ string
-- e ∈ expr ⩴ i                   -- integer literals
--          | e + e               -- plus expressions
--          | e × e               -- times expressions
--          | b                   -- boolean literals
--          | IF b THEN e ELSE e  -- conditional statements
--          | x                   -- variables
--          | LET x ≛ e IN e      -- let binding
--          | FUN (x,…,x) ⇒ e     -- function creation
--          | e(e,…,e)            -- function application
data Expr = IntE Integer
          | PlusE Expr Expr
          | TimesE Expr Expr
          | BoolE Bool
          | IfE Expr Expr Expr
          | VarE String
          | LetE String Expr Expr
          -- new things
          | FunE [String] Expr
          | AppE Expr [Expr]
  deriving (Eq,Ord,Read,Show)

--------------------
-- INTERPRETATION --
--------------------

-- v ∈ value ⩴ i 
--           | b
--           | ⟨FUN (x,…,x) ⇒ e,γ⟩
data Value = IntV Integer
           | BoolV Bool
           | CloV [String] Expr Env
  deriving (Eq,Ord,Read,Show)
--
-- γ ∈ env ≜ var ⇀ value
type Env = Map String Value

-- a ∈ answer ⩴ v | BAD
data Answer = ValA Value
            | BadA
  deriving (Eq,Ord,Read,Show)

-- [E1] ★☆☆
-- In the previous assignment we used the following interpretation for
-- functions:
--
--     interpA(ds,γ,f(e₁,…,eₙ)) ≜ interpA(ds,∅[x₁↦v₁,…,xₙ↦vₙ],e)
--       where  DEF f(x₁,…xₙ) ≛ e = ds(f)
--       and    vᵢ = interpA(ds,γ,eᵢ)
--
-- A direct translation of this into our language with closures is:
--
--     interpA(γ,e₀(e₁,…,eₙ)) ≜ interpA(∅[x₁↦v₁,…,xₙ↦vₙ],e)
--       where ⟨FUN (x₁,…,xₙ) ⇒ e,γ′⟩ = interpA(γ,e₀)
--                                 v₁ = interpA(γ,e₁)
--                                    ⋮
--                                 vₙ = interpA(γ,eₙ)
--
-- We name this `interpA` to distinguish it from other interpreter semantics.
--
-- *THIS DOES NOT DO THE RIGHT THING.* The correct definition of `interp` for
-- function application is:
--
--                                the change
--                                    ⌄⌄
--     interp(γ,e₀(e₁,…,eₙ)) ≜ interp(γ′[x₁↦v₁,…,xₙ↦vₙ],e)
--       where ⟨FUN (x₁,…,xₙ) ⇒ e,γ′⟩ = interp(γ,e₀)
--                                 v₁ = interp(γ,e₁)
--                                    ⋮
--                                 vₙ = interp(γ,eₙ)
--
-- That is, the environment used to interpret the body of the function should
-- be an extension of the *closure* environment γ′, not the empty environment
-- ∅.

-- You must write 5 different expressions that, when evaluted in the empty
-- environment, the interpretation using `interpA` will be differnt than the
-- correct interpretation `interp` described above.
--
-- NOTE: there are no tests for this exercise in the automatic test suite

interpABadE1 :: Expr
interpABadE1 = error "TODO"

interpABadE2 :: Expr
interpABadE2 = error "TODO"

interpABadE3 :: Expr
interpABadE3 = error "TODO"

interpABadE4 :: Expr
interpABadE4 = error "TODO"

interpABadE5 :: Expr
interpABadE5 = error "TODO"

-- [E2] ★☆☆
-- In the first version of the previous assignment we used the following
-- (wrong) interpretation for functions:
--
--                                      the bug
--                                           ⌄
--     interpB(ds,γ,f(e₁,…,eₙ)) ≜ interpB(ds,γ[x₁↦v₁,…,xₙ↦vₙ],e)
--       where  DEF f(x₁,…xₙ) ≛ e = ds(f)
--       and    vᵢ = interpB(ds,γ,eᵢ)
--
-- A direct translation of this into our language with closures is:
--
--     interpB(γ,e₀(e₁,…,eₙ)) ≜ interpB(γ[x₁↦v₁,…,xₙ↦vₙ],e)
--       where ⟨FUN (x₁,…,xₙ) ⇒ e,γ′⟩ = interpB(γ,e₀)
--                                 v₁ = interpB(γ,e₁)
--                                    ⋮
--                                 vₙ = interpB(γ,eₙ)
--
-- We name this `interpB` to distinguish it from other interpreter semantics.
--
-- *THIS DOES NOT DO THE RIGHT THING.* The correct definition of `interp` for
-- function application is:
--
--                                the change
--                                    ⌄⌄
--     interp(γ,e₀(e₁,…,eₙ)) ≜ interp(γ′[x₁↦v₁,…,xₙ↦vₙ],e)
--       where ⟨FUN (x₁,…,xₙ) ⇒ e,γ′⟩ = interp(γ,e₀)
--                                 v₁ = interp(γ,e₁)
--                                    ⋮
--                                 vₙ = interp(γ,eₙ)
--
-- (This is the same “correct” interpreter also shown in E1.)
--
-- That is, the environment used to interpret the body of the function should
-- be an extension of the *closure* environment γ′, not the current evaluation
-- environment γ.

-- You must write 5 different expressions that, when evaluted in the empty
-- environment, the interpretation using `interpB` will be differnt than the
-- correct interpretation described above.
--
-- NOTE: there are no tests for this exercise in the automatic test suite

interpBBadE1 :: Expr
interpBBadE1 = error "TODO"

interpBBadE2 :: Expr
interpBBadE2 = error "TODO"

interpBBadE3 :: Expr
interpBBadE3 = error "TODO"

interpBBadE4 :: Expr
interpBBadE4 = error "TODO"

interpBBadE5 :: Expr
interpBBadE5 = error "TODO"

-- [E3] ★★★
-- You must write a correct interpeter for the current language. (See at the
-- top of the assignemnt definitions in comments for `e ∈ expr`.)
--
-- A definitional description of the interpreter is provided here:
--
-- interp(γ,i) ≜ i
-- interp(γ,e₁ + e₂) ≜ i₁ + i₂
--   where  i₁ = interp(γ,e₁)
--   and    i₂ = interp(γ,e₂)
-- interp(γ,e₁ × e₂) ≜ i₁ × i₂
--   where  i₁ = interp(γ,e₁)
--          i₂ = interp(γ,e₂)
-- interp(γ,b) ≜ b
-- interp(γ,IF e₁ THEN e₂ ELSE e₃) ≜
--   interp(γ,e₂)  when  true = interp(γ,e₁)
--   interp(γ,e₃)  when  false = interp(γ,e₁)
-- interp(γ,x) ≜ γ(x)
-- interp(γ,LET x ≛ e₁ IN e₂) ≜ interp(γ[x↦v],e₂)
--   where  v = interp(ds,γ,e₁)
-- interp(γ,FUN (x₁,…,xₙ) ⇒ e) ≜ ⟨FUN (x₁…,xₙ) ⇒ e,γ⟩
-- interp(γ,e₀(e₁,…,eₙ)) ≜ interp(γ′[x₁↦v₁,…,xₙ↦vₙ],e)
--   where ⟨FUN (x₁,…,xₙ) ⇒ e,γ′⟩ = interp(γ,e₀)
--                             v₁ = interp(γ,e₁)
--                                ⋮
--                             vₙ = interp(γ,eₙ)
--
-- HINT: you may use extendEnv, provided above, for extending an environment
-- with a list of names mapped to a list of answers

-- extendEnv: A helper function for extending an environment given a list of
-- variable names and a list of answers.
--
-- This operation fails (returns Nothing) if (1) the lists are of different
-- lengths, or (2) any of the answers are BAD
extendEnv :: [String] -> [Answer] -> Env -> Maybe Env
extendEnv [] [] env = Just env
extendEnv (_:_) [] env = Nothing
extendEnv [] (_:_) env = Nothing
extendEnv (_:_) (BadA:_) env = Nothing
extendEnv (x:xs) (ValA v:as) env = extendEnv xs as (Map.insert x v env)

-- HINT: You should be able to implement the function application case using
--       the `map` function to interpret the list of expressions `e₁,…,eₙ`.
--       You are welcome to not use `map` and create a helper function if you
--       want.
interp :: Env -> Expr -> Answer
interp env e = error "TODO"

interpTests :: (Int,String,Env -> Expr -> Answer,[((Env,Expr),Answer)])
interpTests =
  let -- LET f = FUN (x) ⇒ x + 1 IN
      -- f(2)
      e1 = LetE "f" (FunE ["x"] (PlusE (VarE "x") (IntE 1))) 
           (AppE (VarE "f") [IntE 2])
      -- 3
      a1 = ValA (IntV 3)
      -- LET y = 1 IN
      -- LET f = FUN(x) ⇒ x + y IN
      -- f(2)
      e2 = LetE "y" (IntE 1) 
           (LetE "f" (FunE ["x"] (PlusE (VarE "x") (VarE "y")))
            (AppE (VarE "f") [IntE 2]))
      -- 3
      a2 = ValA (IntV 3)
      -- LET x = 1 IN
      -- LET f = FUN(x) ⇒ x + 1 IN
      -- f(2)
      e3 = LetE "x" (IntE 1) 
           (LetE "f" (FunE ["x"] (PlusE (VarE "x") (IntE 1)))
            (AppE (VarE "f") [IntE 2]))
      a3 = ValA (IntV 3)
      -- LET f = FUN(x) ⇒ x + 1 IN
      -- LET x = 1 IN
      -- f(2)
      e4 = LetE "f" (FunE ["x"] (PlusE (VarE "x") (IntE 1)))
           (LetE "x" (IntE 1) 
            (AppE (VarE "f") [IntE 2]))
      a4 = ValA (IntV 3)
      -- LET f = FUN(x) ⇒ x + y IN
      -- LET y = 1 IN
      -- f(2)
      e5 = LetE "f" (FunE ["x"] (PlusE (VarE "x") (VarE "y")))
           (LetE "y" (IntE 1) 
            (AppE (VarE "f") [IntE 2]))
      -- BAD
      a5 = BadA
  in
  (3
  ,"interp"
  ,interp
  --   TESTS
  --   initial     expression
  --   env         ⌄⌄    expected answer
  --   ⌄⌄⌄⌄⌄⌄⌄⌄⌄   ⌄⌄    ⌄⌄
  ,[( (Map.empty , e1) , a1 )
   ,( (Map.empty , e2) , a2 )
   ,( (Map.empty , e3) , a3 )
   ,( (Map.empty , e4) , a4 )
   ,( (Map.empty , e5) , a5 )
   -- write your own tests here
   ]
  )

---------------
-- ALL TESTS --
---------------

allTests :: [Test]
allTests =
  [Test2 interpTests
  ]

----------------------
-- MAIN = RUN TESTS --
----------------------

main :: IO ()
main = runTests allTests

----------------------------
-- TESTING INFRASTRUCTURE --
----------------------------

mapOn :: [a] -> (a -> b) -> [b]
mapOn = flip map

foldMOn :: (Foldable t,Monad m) => b -> t a -> (b -> a -> m b) -> m b
foldMOn i xs f = foldM f i xs

data Test where
  Test1 :: (Show a,Eq b,Show b) => (Int,String,a -> b,[(a,b)]) -> Test
  Test2 :: (Show a,Show b,Eq c,Show c) => (Int,String,a -> b -> c,[((a,b),c)]) -> Test
  Test3 :: (Show a,Show b,Show c,Eq d,Show d) => (Int,String,a -> b -> c -> d,[((a,b,c),d)]) -> Test

runTests :: [Test] -> IO ()
runTests ts = do
  rs <- forM ts $ \ t -> do
    y <- case t of
      Test1 t -> runTests1 t
      Test2 t -> runTests2 t
      Test3 t -> runTests3 t
    putStrLn ""
    return y
  forM_ (zip [1..] rs) $ \ (m,(n,passed,failed)) -> do
    when (m /= 1) $ putStrLn ""
    putStrLn $ "++ E" ++ show n ++ " Tests Passed: " ++ show passed
    putStrLn $ "-- E" ++ show n ++ " Tests Failed: " ++ show failed

showTestResult :: (Eq a,Show a) => String -> a -> Either String a -> (Int,Int) -> IO (Int,Int)
showTestResult fx y y'M (passed,failed) = do
  let eM = case y'M of
        Left e -> Just $ "[ERROR]: " ++ e
        Right y' ->
          if y' == y
          then Nothing
          else Just $ show y'
  case eM of
    Nothing -> do
      putStrLn $ "   [TEST PASSED]: " ++ fx
      hFlush stdout
      return (passed+1,failed)
    Just s -> do
      putStrLn $ "   [TEST FAILED]:"
      putStrLn $ "     -- the input"
      putStrLn $ "     " ++ fx
      putStrLn $ "   =="
      putStrLn $ "     -- the output"
      putStrLn $ "     " ++ s
      putStrLn $ "   /="
      putStrLn $ "     -- the expected result"
      putStrLn $ "     " ++ show y
      hFlush stdout
      return (passed,failed+1)

runTestsN :: (Eq a,Show a) => Int -> String -> [(String,() -> a,a)] -> IO (Int,Int,Int)
runTestsN n name tests = do
  putStrLn $ ">> E" ++ show n ++ " Tests: " ++ name
  (passed,failed) <- foldMOn (0,0) tests $ \ pf (s,fx,y) -> do
    y'M <- catch (Right <$> evaluate (fx ())) $ \ (SomeException e) -> return $ Left $ chomp $ unwords $ lines $ show e
    showTestResult s y y'M pf
  return (n,passed,failed)
  where
    chomp s0 = concat $ mapOn (group s0) $ \ s ->
      if " " `isPrefixOf` s then " " else s

runTests1 :: (Eq b,Show a,Show b) => (Int,String,a -> b,[(a,b)]) -> IO (Int,Int,Int)
runTests1 (n,name,f,tests) = runTestsN n name $ mapOn tests $ \ (x,y) ->
  (name ++ " " ++ showsPrec 11 x [],\() -> f x,y)

runTests2 :: (Eq c,Show a,Show b,Show c) => (Int,String,a -> b -> c,[((a,b),c)]) -> IO (Int,Int,Int)
runTests2 (n,name,f,tests) = runTestsN n name $ mapOn tests $ \ ((x,y),z) ->
  (name ++ " " ++ showsPrec 11 x [] ++ " " ++ showsPrec 11 y [],\() -> f x y,z)

runTests3 :: (Eq d,Show a,Show b,Show c,Show d) => (Int,String,a -> b -> c -> d,[((a,b,c),d)]) -> IO (Int,Int,Int)
runTests3 (n,name,f,tests) = runTestsN n name $ mapOn tests $ \ ((w,x,y),z) ->
  (name ++ " " ++ showsPrec 11 w [] ++ " " ++ showsPrec 11 x [] ++ " " ++ showsPrec 11 y [],\() -> f w x y,z)

