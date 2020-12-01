{-# LANGUAGE GADTs #-} -- used in testing infrastructure
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Hw06 where

{-

v1.1

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
--          | BOX(e)              -- box creation
--          | !e                  -- unboxing (de-reference)
--          | e ← e               -- assignment
data Expr = IntE Integer
          | PlusE Expr Expr
          | TimesE Expr Expr
          | BoolE Bool
          | IfE Expr Expr Expr
          | VarE String
          | LetE String Expr Expr
          | FunE [String] Expr
          | AppE Expr [Expr]
          -- new things
          | BoxE Expr
          | UnboxE Expr
          | AssignE Expr Expr
  deriving (Eq,Ord,Read,Show)

--------------------
-- INTERPRETATION --
--------------------

-- ℓ ∈ location ≜ ℕ
-- NOTE: we use integers to represent locations, but all locations should be
--       strictly non-negative integers (i.e., natural numbers)
type Location = Integer

-- v ∈ value ⩴ i 
--           | b
--           | ⟨FUN (x,…,x) ⇒ e,γ⟩
--           | ℓ
data Value = IntV Integer
           | BoolV Bool
           | CloV [String] Expr Env
           | LocV Location
  deriving (Eq,Ord,Read,Show)

-- γ ∈ env ≜ var ⇀ value
type Env = Map String Value

-- σ ∈ store ≜ location ⇀ value
type Store = Map Location Value

-- a ∈ answer ⩴ ⟨v,σ⟩ | BAD
data Answer = ValA Value Store
            | BadA
  deriving (Eq,Ord,Read,Show)

-- [E1] ★☆☆
-- fresh-integer ∈ list(ℕ) → ℕ
-- fresh-integer [n₁,…,nₙ] ≈ n
--   where
--     n = MAX [0,n₁+1,…,nₙ+1]
-- HINT: implement this function by recursion on the list of natural numbers
--       (represented as Haskell integers)
freshInteger :: [Integer] -> Integer
freshInteger ns = error "TODO"

freshIntegerTests :: (Int,String,[Integer] -> Integer,[([Integer],Integer)])
freshIntegerTests =
  (1
  ,"freshInteger"
  ,freshInteger
  ,[( []          , 0 )
   ,( [1]         , 2 )
   ,( [1,2]       , 3 )
   ,( [2,1]       , 3 )
   ,( [2]         , 3 )
   ,( [3,2,1]     , 4 )
   -- write your own tests here
   ]
  )

-- [E2] ★☆☆
-- fresh-loc ∈ (location ⇀ value) → ℕ
-- fresh-loc {ℓ₁ ↦ v₁,…,ℓₙ ↦ vₙ} ≜ fresh-integer [ℓ₁,…,ℓₙ]
-- HINT: use `freshInteger` from E1
-- HINT: you may find the following function for maps useful:
--
--     Map.keys :: Map k v -> [k]
--
freshLoc :: Store -> Integer
freshLoc store = error "TODO"

freshLocTests :: (Int,String,Store -> Integer,[(Store,Integer)])
freshLocTests =
  (2
  ,"freshLoc"
  ,freshLoc
  ,[( Map.empty                            , 0 )
   ,( Map.fromList [(1,IntV 1)]            , 2 )
   ,( Map.fromList [(1,IntV 1),(2,IntV 1)] , 3 )
   ,( Map.fromList [(2,IntV 1),(1,IntV 1)] , 3 )
   ,( Map.fromList [(2,IntV 100)]          , 3 )
   -- write your own tests here
   ]
  )

-- [E3] ★★★
-- interp ∈ env × store × expr → answer
-- interp(γ,σ,i) ≜ ⟨i,σ⟩
-- interp(γ,σ,e₁ + e₂) ≜ ⟨i₁+i₂,σ″⟩
--   where ⟨i₁,σ′⟩ = interp(γ,σ,e₁)
--   and   ⟨i₂,σ″⟩ = interp(γ,σ′,e₂)
-- interp(γ,σ,e₁ × e₂) ≜ ⟨i₁⋅i₂,σ″⟩
--   where ⟨i₁,σ′⟩ = interp(γ,σ,e₁)
--   and   ⟨i₂,σ″⟩ = interp(γ,σ′,e₂)
-- interp(γ,σ,b) ≜ ⟨b,σ⟩
-- interp(γ,σ,IF e₁ THEN e₂ ELSE e₃) ≜ interp(γ,σ′,e₂)
--   when ⟨true,σ′⟩ = interp(γ,σ,e₁)
-- interp(γ,σ,IF e₁ THEN e₂ ELSE e₃) ≜ interp(γ,σ′,e₃)
--   when ⟨false,σ′⟩ = interp(γ,σ,e₁)
-- interp(γ,σ,x) ≜ γ(x)
-- interp(γ,σ,LET x = e₁ in e₂) ≜ interp(γ[x↦v],σ′,e₂)
--   where
--     ⟨v,σ′⟩ = interp(γ,σ,e₁)
-- interp(γ,σ,FUN (x₁,…,xₙ) ⇒ e) ≜ ⟨ ⟨FUN (x₁,…,xₙ) ⇒ e , γ⟩ , σ ⟩
-- interp(γ,σ,e(e₁,…,eₙ)) ≜ apply(γ,σ′,[e₁,…,eₙ],[x₁,…,xₙ],e′,γ′)
--   where ⟨⟨FUN (x₁,…,xₙ) ⇒ e , γ′⟩,σ′⟩ = interp(γ,σ,e)
-- interp(γ,σ,BOX(e)) ≜ ⟨ℓ,σ′[ℓ↦v]⟩
--   where ⟨v,σ′⟩ = interp(γ,σ,e)
--         ℓ = fresh-loc(σ′)
-- interp(γ,σ,!e) ≜ ⟨σ′(ℓ),σ′⟩
--   where ⟨ℓ,σ′⟩ = interp(γ,σ,e)
-- interp(γ,σ,e₁ ← e₂) ≜ ⟨v,σ″[ℓ↦v]⟩
--   where ⟨ℓ,σ′⟩ = interp(γ,σ,e₁)
--         ⟨v,σ″⟩ = interp(γ,σ′,e₂)
-- HINT: Solutions for integer literals, plus expressions, function
--       application, are provided for you. Use the implementation of those
--       cases to help you plan your solution to the other cases.
interp :: Env -> Store -> Expr -> Answer
interp env store (IntE i) = ValA (IntV i) store
interp env store (PlusE e1 e2) = case interp env store e1 of
  ValA (IntV i1) store' -> case interp env store' e2 of
    ValA (IntV i2) store'' -> ValA (IntV (i1 + i2)) store''
    _ -> BadA
  _ -> BadA
interp env store (TimesE e1 e2) = error "TODO"
interp env store (BoolE b) = error "TODO"
interp env store (IfE e1 e2 e3) = error "TODO"
interp env store (VarE x) = error "TODO"
interp env store (LetE x e1 e2) = error "TODO"
interp env store (FunE xs e) = error "TODO"
interp env store (AppE e es) = case interp env store e of
  ValA (CloV xs e' env') store' -> apply env store' es xs e' env'
  _ -> BadA
interp env store (BoxE e) = case interp env store e of
  ValA v store' ->
    let l = freshLoc store' in 
    ValA (LocV l) (Map.insert l v store')
  _ -> BadA
interp env store (UnboxE e) = error "TODO"
interp env store (AssignE e1 e2) = error "TODO"

interpTests :: (Int,String,Expr -> Answer,[(Expr,Answer)])
interpTests =
  (3
  ,"interp"
  ,interp Map.empty Map.empty

  -- in each test: interp(e) = ⟨v,σ⟩
  --
  ,[ -- e = LET x = BOX 10 IN x
    ( LetE "x" (BoxE (IntE 10)) (VarE "x")
    , ValA 
      -- v = LOC(0)
      (LocV 0) 
      -- σ = {0 ↦ 10}
      (Map.fromList [(0,IntV 10)])
    )
    -- e = LET x = BOX 10 IN !x
   ,( LetE "x" (BoxE (IntE 10)) (UnboxE (VarE "x"))
    , ValA
      -- v = 10
      (IntV 10)
      -- σ = {0 ↦ 10}
      (Map.fromList [(0,IntV 10)])
    )
   -- e = LET x = BOX 10 IN 
   --     LET y = BOX 20 IN
   --     (x ← !y) + !x
   ,( LetE "x" (BoxE (IntE 10))
      (LetE "y" (BoxE (IntE 20))
      (PlusE (AssignE (VarE "x") (UnboxE (VarE "y"))) (UnboxE (VarE "x"))))
    , ValA
      -- v = 40
      (IntV 40)
      (Map.fromList [(0,IntV 20),(1,IntV 20)])
    )
   -- e = LET x = BOX 10 IN 
   --     LET y = BOX 20 IN
   --     (x ← !y) × !x
   ,( LetE "x" (BoxE (IntE 10))
      (LetE "y" (BoxE (IntE 20))
      (TimesE (AssignE (VarE "x") (UnboxE (VarE "y"))) (UnboxE (VarE "x"))))
    , ValA
      -- v = 40
      (IntV 400)
      (Map.fromList [(0,IntV 20),(1,IntV 20)])
    )
   -- e = LET x = BOX false IN 
   --     LET y = BOX 20 IN
   --     IF (x ← true) THEN !x ELSE (y ← 100))
   ,( LetE "x" (BoxE (BoolE False))
      (LetE "y" (BoxE (IntE 20))
      (IfE (AssignE (VarE "x") (BoolE True)) 
           (UnboxE (VarE "x"))
           (AssignE (VarE "y") (IntE 100))))
    , ValA
      -- v = 40
      (BoolV True)
      (Map.fromList [(0,BoolV True),(1,IntV 20)])
    )
   ]
  )

-- HELPER
-- apply ∈ env × store × list(expr) × list(var) × expr × env → answer
apply :: Env -> Store -> [Expr] -> [String] -> Expr -> Env -> Answer
apply env store []     []     e' env' = interp env' store e'
apply env store (_:_)  []     e' env' = BadA
apply env store []     (_:_)  e' env' = BadA
apply env store (e:es) (x:xs) e' env' = case interp env store e of
  ValA v store' -> apply env store es xs e' (Map.insert x v env')
  _ -> BadA

---------------
-- ALL TESTS --
---------------

allTests :: [Test]
allTests =
  [Test1 freshIntegerTests
  ,Test1 freshLocTests
  ,Test1 interpTests
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
