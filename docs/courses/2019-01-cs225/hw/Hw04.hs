{-# LANGUAGE GADTs #-} -- used in testing infrastructure
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Hw04 where

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

-- NOTE:
--
-- In syntax, we will write equal signs as `≛` and not `=`, so that syntax `=`
-- is not confused with math `=`.
--
-- i ∈ ℤ ≜ {…,-2,-1,0,1,2,…}
-- b ∈ 𝔹 ≜ {true,false}
-- i ∈ ℤ
-- x ∈ var      ≜ string
-- f ∈ fun-name ≜ string
-- e ∈ expr ⩴ i                   -- integer literals
--          | e + e               -- plus expressions
--          | e × e               -- times expressions
--          | b                   -- boolean literals
--          | IF b THEN e ELSE e  -- conditional statements
--          | x                   -- variables
--          | LET x ≛ e IN e      -- let binding
--          | f(e,…,e)            -- function application

data Expr = IntE Integer
          | PlusE Expr Expr
          | TimesE Expr Expr
          | BoolE Bool
          | IfE Expr Expr Expr
          -- new things
          | VarE String
          | LetE String Expr Expr
          | AppE String [Expr]
  deriving (Eq,Ord,Read,Show)

-- d ∈ defn ⩴ DEF f(x,…,x) ≛ e        -- function definition
data Defn = Defn String [String] Expr
  deriving (Eq,Ord,Read,Show)

-- p ∈ prog ⩴ d ; ⋯ ; d ; e       -- a complete program
data Prog = Prog [Defn] Expr

--------------------
-- INTERPRETATION --
--------------------

-- v ∈ value ⩴ i | b
data Value = IntV Integer
           | BoolV Bool
  deriving (Eq,Ord,Read,Show)

-- a ∈ answer ⩴ v | BAD
data Answer = ValA Value
            | BadA
  deriving (Eq,Ord,Read,Show)

-- γ ∈ env ≜ var ⇀ value
type Env = Map String Value

-- [E1] ★☆☆
-- get-defn ∈ fun-name × list(defn) ⇀ defn
--
-- get-defn(f,ds) should return the definition `d` in the list of definitions
-- `ds` such that the function name of `d` is `f`.
--
-- (note, this is not a definition of `get-def`; this is a specification!)
--
-- get-defn(f,ds) ≡ d
--     if and only if  d ∈ ds
--     and             d = DEF f(x₁,…,xₙ) ≛ e
--     for some        `x₁,…,xₙ` and `e`
--
-- HINT: pattern match on the structure of the second argument--the list of
-- definitions. There should be two cases. In the empty list case you should
-- return `Nothing`, and in the non-empty list case you should have two
-- subcases: (1) the name matches the one you are looking for, so return `Just
-- d` for the definition `d`, or (2) the name does not match the one you are
-- looking for, so do a recursive call to search the remainder of the list.
--
-- Remember, the two cases for lists are:
--   [] -> undefined -- the empty list case
--   x:xs -> undefined -- the non-empty list case
--   ^  ^
--   |  |
--   |  the rest of the list
--   an element of the list
getDefn :: String -> [Defn] -> Maybe Defn
getDefn x defs = undefined

getDefnTests :: (Int,String,String -> [Defn] -> Maybe Defn,[((String,[Defn]),Maybe Defn)])
getDefnTests =
  let f = Defn "f" ["x","y"] (VarE "x")
      g = Defn "g" ["a","b"] (VarE "y")
      h = Defn "h" ["c","d"] (PlusE (VarE "c") (VarE "d"))
      defns = [f,g,h]
  in
  (1
  ,"getDefn"
  ,getDefn
  ,[( ("f",defns) , Just f  )
   ,( ("g",defns) , Just g  )
   ,( ("h",defns) , Just h  )
   ,( ("i",defns) , Nothing )
   ,( ("x",defns) , Nothing )
   ,( ("a",defns) , Nothing )
   -- write your own tests here
   ]
  )

-- [E2] ★★☆
-- extend-env ∈ list(var) × list(answer) × env ⇀ env
--
-- extend-env(xs,as,γ) should return a new environment which contains all of
-- the mappings from γ, as well as each pairwise mapping xᵢ ↦ aᵢ for xᵢ ∈ xs
-- and aᵢ ∈ as. If xs and as are lists of different length, this function is
-- undefined (i.e., should return `Nothing`)
--
-- (note, this is not a definition of `extend-env`; this is a specification!)
--
-- extend-env((x₁,…,xₙ),(a₁,…,aₙ),γ) ≡ γ′
--     if and only if  aᵢ = vᵢ
--     and             γ′(xᵢ) = vᵢ
--     and             γ′(x) = γ(x)  for  x ∉ x₁,…,xₙ
--
-- HINT: pattern match on both list arguments. You should have 4 cases (2 cases
-- for each list; 2×2=4). Two cases represent when the length of the two lists
-- are not the same. Return `Nothing` in these cases
--
-- HINT: you may find the `Map.insert` function useful. `Map.insert x v m`
-- inserts the mapping (x↦v) into the map m. To see the type of Map.insert,
-- type `:t Map.insert` after loading this file with `stack ghci <this file>`
extendEnv :: [String] -> [Answer] -> Env -> Maybe Env
extendEnv xs as env = undefined

extendEnvTests :: (Int,String,[String] -> [Answer] -> Env -> Maybe Env,[(([String],[Answer],Env),Maybe Env)])
extendEnvTests =
  let env = Map.fromList [("x",IntV 1),("y",IntV 2)]
  in
  (2
  ,"extendEnv"
  ,extendEnv
  ,[( (["a","b"] , [ValA (IntV 10),ValA (BoolV True)] , env) , Just
                                                               (Map.fromList [("x",IntV 1)
                                                                             ,("y",IntV 2)
                                                                             ,("a",IntV 10)
                                                                             ,("b",BoolV True)
                                                                             ]))
   ,( (["x","z"] , [ValA (IntV 10),ValA (BoolV True)] , env) , Just
                                                               (Map.fromList [("x",IntV 10)
                                                                             ,("y",IntV 2)
                                                                             ,("z",BoolV True)
                                                                             ]))
   ,( (["x","y"] , [ValA (IntV 10),ValA (BoolV True)] , env) , Just
                                                               (Map.fromList [("x",IntV 10)
                                                                             ,("y",BoolV True)
                                                                             ]))
   ,( (["a","b"] , [ValA (IntV 10)]                   , env) , Nothing )
   ,( (["a"]     , [ValA (IntV 10),ValA (BoolV True)] , env) , Nothing )
   ,( (["a","b"] , [ValA (IntV 10),BadA]              , env) , Nothing )
   -- write your own tests here
   ]
  )

-- [E3] ★★★
-- interp ∈ list(defn) × env × expr → answer
--
-- interp(ds,γ,e) interprets the expression e where env is used to interpret
-- variables inside e, and ds is used to interpret function calls inside e.
--
-- interp(ds,γ,i) ≜ i
-- interp(ds,γ,e₁ + e₂) ≜ i₁ + i₂
--   where  i₁ = interp(ds,γ,e₁)
--   and    i₂ = interp(ds,γ,e₂)
-- interp(ds,γ,e₁ × e₂) ≜ i₁ × i₂
--   where  i₁ = interp(ds,γ,e₁)
--          i₂ = interp(ds,γ,e₂)
-- interp(ds,γ,b) ≜ b
-- interp(ds,γ,IF e₁ THEN e₂ ELSE e₃) ≜
--   interp(ds,γ,e₂)  when  interp(ds,γ,e₁) = true
--   interp(ds,γ,e₃)  when  interp(ds,γ,e₁) = false
-- interp(ds,γ,x) ≜ γ(x)
-- interp(ds,γ,LET x ≛ e₁ IN e₂) ≜ interp(ds,γ[x↦v],e₂)
--   where  v = interp(ds,γ,e₁)
-- interp(ds,γ,f(e₁,…,eₙ)) ≜ interp(ds,{x₁↦v₁,…,xₙ↦vₙ},e)
--   where  DEF f(x₁,…xₙ) ≛ e = ds(f)
--   and    vᵢ = interp(ds,γ,eᵢ)
--
-- HINT: in the case for variables, you should return BadA if the variable is
-- not found in the environment (i.e., if it is "out of scope")
-- HINT: you may find Map.insert comes in handy in the case for let expressions
-- HINT: use `extendEnv` on the empty map in the case for function application
-- HINT: you may need to create a helper function in the function application
--       case to iterate (via recursion) over the list of expression arguments.
--       You don't need to use a helper function if you want to use `map`.
interp :: [Defn] -> Env -> Expr -> Answer
interp defs env e = undefined

interpTests :: (Int,String,[Defn] -> Env -> Expr -> Answer,[(([Defn],Env,Expr),Answer)])
interpTests =
  let defs =
        [ Defn "f" ["x","y"] (PlusE (VarE "x") (VarE "y"))
        , Defn "g" ["x","y"] (TimesE (VarE "x") (VarE "y"))
        , Defn "h" ["x","y"] (AppE "f" [AppE "g" [VarE "x",VarE "x"],AppE "g" [VarE "y",VarE "y"]])
        ]
      e1 = AppE "f" [IntE 1,IntE 2]
      a1 = ValA (IntV 3)
      e2 = AppE "g" [IntE 1,IntE 2]
      a2 = ValA (IntV 2)
      e3 = AppE "f" [AppE "g" [IntE 1,IntE 2],IntE 3]
      a3 = ValA (IntV 5)
      e4 = LetE "x" (PlusE (IntE 1) (IntE 1)) $
           LetE "y" (PlusE (IntE 2) (IntE 2)) $
           AppE "h" [VarE "x",VarE "y"]
      a4 = ValA (IntV 20)
      e5 = AppE "f" [IntE 1]
      a5 = BadA
      e6 = AppE "f" [IntE 1,IntE 2,IntE 3]
      a6 = BadA
  in
  (3
  ,"interp"
  ,interp
  ,[( (defs , Map.empty , e1) , a1 )
   ,( (defs , Map.empty , e2) , a2 )
   ,( (defs , Map.empty , e3) , a3 )
   ,( (defs , Map.empty , e4) , a4 )
   ,( (defs , Map.empty , e5) , a6 )
   ,( (defs , Map.empty , e5) , a6 )
   -- write your own tests here
   ]
  )

---------------
-- ALL TESTS --
---------------

allTests :: [Test]
allTests =
  [Test2 getDefnTests
  ,Test3 extendEnvTests
  ,Test3 interpTests
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
