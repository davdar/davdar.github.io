{-# LANGUAGE GADTs #-} -- used in testing infrastructure
module Hw02 where

{- 

HW2 v1.0

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

-- We are going to add conditionals to our language. Here is the formal
-- langauge specification:
-- 
-- b ∈ 𝔹 ≜ {true,false}
-- i ∈ ℤ
-- e ∈ expr ⩴ i
--          | e + e
--          | e × e
--          | b
--          | IF b THEN e ELSE e

data Expr = IntE Integer
          | PlusE Expr Expr 
          | TimesE Expr Expr
          -- new things
          | BoolE Bool
          | IfE Expr Expr Expr
  deriving (Eq,Ord,Read,Show)

-- We now have two types of values: integers and booleans. (Before we didn't
-- bother to define a special type for values, because the only type of value
-- was an integer.)
--
-- v ∈ value ⩴ i | b

data Value = IntV Integer
           | BoolV Bool
  deriving (Eq,Ord,Read,Show)

-- Programs can now fail due to a type error, so the result of
-- interpretation—called an “answer”—is now either a value or a special answer
-- symbol `BAD`
--
-- a ∈ answer ⩴ v | BAD

data Answer = ValueA Value
            | BadA
  deriving (Eq,Ord,Read,Show)

-- [E1]
-- We are ready to define the new interpreter. Note that the structure has
-- changed in the following ways:
-- ‣ There are two new language features, boolean literals and if statements
-- ‣ The result of interpretation is not always an integer. The result is an
--   “answer” which is either `BAD` or value, and values are either integers or
--   booleans.
-- *Make sure that when you run this file there are no warnings about “missing
-- cases”.*
-- Some notes on how to define the interpreter:
-- ‣ The interpretation of `IF i THEN e₁ ELSE e₂` for some integer `i` should be `BAD`
-- ‣ Adding or multiplying an integer with a boolean should result in `BAD`
-- ‣ `IF true THEN 1 ELSE 1 + false` should result in `1`
-- ‣ `IF false THEN 1 ELSE 1 + false` should result in `BAD`
-- ‣ `IF b THEN 1 ELSE false` should *not* result in `BAD` for any boolean `b`
-- *You should write your own tests cases based on the above to test your
-- interpreter.*
--
-- interp(e₁ + e₂) ≜ i₁ + i₂
--   when
--     i₁ = interp(e₁) 
--     i₂ = interp(e₂)
--
interp :: Expr -> Answer
interp e0 = case e0 of
  IntE i -> error "TODO"
  PlusE e1 e2 -> case (interp e1, interp e2) of
    (ValueA (IntV i1), ValueA (IntV i2)) -> ValueA (IntV (i1 + i2))
    _ -> BadA
  TimesE e1 e2 -> error "TODO"
  BoolE b -> error "TODO"
  IfE e1 e2 e3 -> error "TODO"

interpTests :: (Int,String,Expr -> Answer,[(Expr,Answer)])
interpTests =
  (1
  ,"interp"
  ,interp
  , [(IntE 1,ValueA (IntV 1))
    ,(PlusE (IntE 2) (IntE 3),ValueA (IntV 5))
    ,(IfE (BoolE False) (IntE 1) (IntE 2),ValueA (IntV 2))
    ,(IfE (IntE 1) (IntE 2) (IntE 3),BadA)
    -- <<Add your own tests here>>
    --
    ]
  )

---------------
-- ALL TESTS --
---------------

allTests :: [Test]
allTests =
  [Test1 interpTests]

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
  Test1 :: (Eq b,Show a,Show b) => (Int,String,a -> b,[(a,b)]) -> Test
  Test2 :: (Eq c,Show a,Show b,Show c) => (Int,String,a -> b -> c,[((a,b),c)]) -> Test

runTests :: [Test] -> IO ()
runTests ts = do
  rs <- forM ts $ \ t -> do
    y <- case t of
      Test1 t -> runTests1 t
      Test2 t -> runTests2 t
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
runTests1 (n,name,f,tests) = runTestsN n name $ mapOn tests $ \ (x,y) -> (name ++ " " ++ show x,\() -> f x,y)

runTests2 :: (Eq c,Show a,Show b,Show c) => (Int,String,a -> b -> c,[((a,b),c)]) -> IO (Int,Int,Int)
runTests2 (n,name,f,tests) = runTestsN n name $ mapOn tests $ \ ((x,y),z) -> (name ++ " " ++ show x ++ " " ++ show y,\() -> f x y,z)

