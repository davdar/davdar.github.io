{-# LANGUAGE GADTs #-} -- used in testing infrastructure
module Hw03 where

{- 

v1.0

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

-- We are going to add conditionals to our language. Here is the formal
-- langauge specification:
-- 
-- b ∈ 𝔹 ≜ {true,false}
-- i ∈ ℤ
-- x ∈ var ≜ string
-- e ∈ expr ⩴ i
--          | e + e
--          | e × e
--          | b
--          | IF b THEN e ELSE e
--          | x
--          | LET x = e IN e

data Expr = IntE Integer
          | PlusE Expr Expr 
          | TimesE Expr Expr
          | BoolE Bool
          | IfE Expr Expr Expr
          -- new things
          | VarE String
          | LetE String Expr Expr
  deriving (Eq,Ord,Read,Show)

-- v ∈ value ⩴ i | b

data Value = IntV Integer
           | BoolV Bool
  deriving (Eq,Ord,Read,Show)

-- a ∈ answer ⩴ v | BAD

data Answer = ValA Value
            | BadA
  deriving (Eq,Ord,Read,Show)

-- [E1] ★★☆
-- free-vars ∈ expr → ℘(var)
--
-- free-vars(i)                     ≜ ∅
-- free-vars(e₁ + e₂)               ≜ free-vars(e₁) ∪ free-vars(e₂)
-- free-vars(e₁ × e₂)               ≜ free-vars(e₁) ∪ free-vars(e₂)
-- free-vars(b)                     ≜ ∅
-- free-vars(IF e₁ THEN e₂ ELSE e₃) ≜ free-vars(e₁) ∪ free-vars(e₂) ∪ free-vars(e₃)
-- free-vars(x)                     ≜ {x}
-- free-vars(LET x = e₁ IN e₂)      ≜ free-vars(e₁) ∪ (free-vars(e₂) ∖ {x})
freeVars :: Expr -> Set String
freeVars e = error "TODO"

freeVarsTests :: (Int,String,Expr -> Set String,[(Expr,Set String)])
freeVarsTests =
  (1
  ,"freeVars"
  ,freeVars
  ,[(VarE "x"                                          , Set.fromList ["x"])
   ,(LetE "x" (VarE "y") (VarE "x")                    , Set.fromList ["y"])
   ,(LetE "x" (VarE "x") (VarE "y")                    , Set.fromList ["x","y"])
   ,(PlusE (LetE "x" (VarE "y") (VarE "x")) (VarE "z") , Set.fromList ["y","z"])
   ,(TimesE (IntE 1) (BoolE True)                      , Set.fromList [])
   -- <<Add your own tests here>>
   --
   ]
  )

-- [E2] ★☆☆
-- is-closed(e) ≜ free-vars(e) = ∅
isClosed :: Expr -> Bool
isClosed e = error "TODO"

isClosedTests :: (Int,String,Expr -> Bool,[(Expr,Bool)])
isClosedTests =
  (2
  ,"isClosed"
  ,isClosed
  ,[(VarE "x"                     , False)
   ,(LetE "x" (IntE 1) (VarE "x") , True)
   ,(PlusE (VarE "x") (IntE 1)    , False)
   ,(TimesE (IntE 1) (BoolE True) , True)
   ]
  )

-- [E3] ★★★
-- subst ∈ var × expr × expr → expr
--
-- e = subst(x,e₁,e₂)
-- PRECONDITIONS (you don't need to check them, and you can assume them)
--   + is-closed(e₁)
--   + free-vars(e₂) = X⊎{x}
-- POSTCONDITIONS (you don't need to check them, but you should ensure them)
--   + free-vars(subst(x,e₁,e₂)) = X
--
-- subst(x,e₁,i)                            ≜ i
-- subst(x,e₁,e₂₁ + e₂₂)                    ≜ subst(x,e₁,e₂₁) + subst(x,e₁,e₂₂)
-- subst(x,e₁,e₂₁ ⨯ e₂₂)                    ≜ subst(x,e₁,e₂₁) ⨯ subst(x,e₁,e₂₂)
-- subst(x,e₁,b)                            ≜ b
-- subst(x,e₁,IF e₂₁ THEN e₂₂ ELSE e₂₃)     ≜ IF subst(x,e₁,e₂₁) THEN subst(x,e₁,e₂₂) ELSE subst(x,e₁,e₂₃)
-- subst(x,e₁,x′) | x = x′                  ≜ e₁
-- subst(x,e₁,x′) | x ≠ x′                  ≜ x′
-- subst(x,e₁,LET x′ = e₂₁ IN e₂₂) | x = x′ ≜ LET x′ = subst(x,e₁,e₂₁) IN e₂₂
-- subst(x,e₁,LET x′ = e₂₁ IN e₂₂) | x ≠ x′ ≜ LET x′ = subst(x,e₁,e₂₁) IN subst(x,e₁,e₂₂)
subst :: String -> Expr -> Expr -> Expr
subst x e1 e2 = error "TODO"

substTests :: (Int,String,String -> Expr -> Expr -> Expr,[((String,Expr,Expr),Expr)])
substTests =
  (3
  ,"subst"
  ,subst
  -- the first one is testing…
  -- "substitute "x" for "1" in the program "x", and test that the result is the program "1"
  ,[(("x" , IntE 1                       , VarE "x"                     ) , IntE 1)
   ,(("x" , IntE 1                       , VarE "y"                     ) , VarE "y")
   ,(("x" , IntE 1                       , LetE "x" (IntE 2) (VarE "x") ) , LetE "x" (IntE 2) (VarE "x"))
   ,(("x" , LetE "y" (IntE 1) (VarE "y") , PlusE (VarE "z") (VarE "x")  ) , PlusE (VarE "z") (LetE "y" (IntE 1) (VarE "y")))
   ]
  )

---------------
-- ALL TESTS --
---------------

allTests :: [Test]
allTests =
  [Test1 freeVarsTests
  ,Test1 isClosedTests
  ,Test3 substTests
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


