{-# LANGUAGE GADTs #-} -- used in testing infrastructure
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Hw07 where

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

import Data.Map (Map)
import qualified Data.Map as Map

import Data.List          -- used in testing infrastructure
import Control.Monad      -- used in testing infrastructure
import Control.Exception  -- used in testing infrastructure
import System.IO          -- used in testing infrastructure

import qualified Debug.Trace as Debug

-- ========================================================================= --
-- There is one problem in this assignment with four cases to complete. The
-- cases you need to complete are labeled `error "TODO"`. There are lots of new
-- definitions and helper functions which you will need to understand in order
-- to complete the assignment. Descriptions for all of these new definitions
-- are provided.
--
-- There is one extra credit problem `X1`.
-- ========================================================================= --

-- Variable names
-- x ∈ vname ≈ symbol
type VName = String
-- Class names
-- cn ∈ cname ≈ symbol
type CName = String
-- Field names
-- fn ∈ fname ≈ symbol
type FName = String
-- Method names
-- mn ∈ mname ≈ symbol
type MName = String

-- Expressions
-- e ∈ expr ⩴ i | e + e | e × e 
--          | x | LET x = e IN e
--          | NEW cn(e,…,e)
--          | e.fn
--          | e.fn ← e
--          | e.mn(e)    -- all methods take exactly one argument
--
-- NOTE: in this language, the “this” expression is not a special expression,
--       rather it is just a special element in the set of varaibles.
data Expr = 
     IntE Integer
  |  PlusE Expr Expr
  |  TimesE Expr Expr
  |  VarE VName
  |  LetE VName Expr Expr
  |  NewE CName [Expr]
  |  GetFieldE Expr FName
  |  SetFieldE Expr FName Expr
  |  CallE Expr MName Expr
  deriving (Eq,Ord,Show)

-- A sequence expression—written as a semicolon in concrete syntax—is syntactic
-- sugar for a let statement with a variable name that is not used
-- (e₁ ; e₂) ≜ LET _ = e₁ IN e₂
seqE :: Expr -> Expr -> Expr
seqE e1 e2 = LetE "_" e1 e2

-- class declaration     
-- cd ∈ cdecl ⩴ CLASS cn FIELDS fn … fn ~ md … md
--
--                       field 
--                       names
--                       ⌄⌄⌄⌄⌄⌄⌄
data CDecl = CDecl CName [FName] [MDecl]
--                 ^^^^^         ^^^^^^^
--                 class         method
--                 name          declarations
  deriving (Eq,Ord,Show)

-- method declaration
-- md ∈ mdecl ⩴ METHOD mn(x) ⇒ e
--
--                       parameter 
--                       name
--                       ⌄⌄⌄⌄⌄
data MDecl = MDecl MName VName Expr
--                 ^^^^^       ^^^^
--                 method      method 
--                 name        body
  deriving (Eq,Ord,Show)

-- (See test suite for some example class declarations, method declarations,
-- and expressions that use them.)

-- programs
-- p ∈ prog ⩴ cd … cd DO e
--                       main
--                       expression
--                       ⌄⌄⌄⌄
data Prog = Prog [CDecl] Expr
--               ^^^^^^^
--               class
--               declarations
  deriving (Eq,Ord,Show)

-- object values
-- o ∈ object ⩴ OBJECT cn({fn↦ℓ,…,fn↦ℓ}) {mn↦[FUN(x)⇒e],…,mn↦[FUN(x)⇒e]}
--                         field map
--                         ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄
data Object = Object CName (Map FName Loc) (Map MName (VName,Expr))
--                   ^^^^^                 ^^^^^^^^^^^^^^^^^^^^^^^^
--                   class                 method map
--                   name
  deriving (Eq,Ord,Show)
-- NOTE: Object values contain a field map which maps field names to locations.
-- The locations here are the mutable cell that corresponds to that field.
-- The interpretation of GetFieldE and SetFieldE should interact with this
-- store location in the field map.
 
-- values
-- v ∈ value ⩴ i | o
data Value = IntV Integer
           | ObjectV Object
  deriving (Eq,Ord,Show)

-- locations (domain of the store)
-- ℓ ∈ loc ≈ ℕ
type Loc = Integer
-- environment (maps variable names to values)
-- γ ∈ env ≜ vname ⇀ value
type Env = Map VName Value
-- store (maps locations to values)
-- σ ∈ store ≜ loc ⇀ value
type Store = Map Loc Value

-- allocate a fresh location in the store
freshLoc :: Store -> Loc
freshLoc store = maximum ((-1):Map.keys store) + 1

-- Allocates a value to fresh location in the store. Returns the fresh location
-- that was generated, and the updated store which maps that location to the
-- value argument.
alloc :: Store -> Value -> (Loc,Store)
alloc store v =
  let l = freshLoc store
  in (l,Map.insert l v store)

-- Perform `alloc` on a list of values.
allocMany :: Store -> [Value] -> ([Loc],Store)
allocMany store [] = ([],store)
allocMany store (v:vs) =
  let (l,store') = alloc store v
      (ls,store'') = allocMany store' vs
  in (l:ls,store'')

-- Lookup the class declaration that corresponds to the given name. Returns
-- `Nothing` if there is no class with the argument name.
lookupClass :: [CDecl] -> CName -> Maybe CDecl
lookupClass [] _ = Nothing
lookupClass (CDecl cn fns mds:cds) cn' | cn == cn' = Just (CDecl cn fns mds)
lookupClass (CDecl cn fns mds:cds) cn' | otherwise = lookupClass cds cn'

-- Constructs a field map from a list of field names and a list of locations.
buildFieldMap :: [FName] -> [Loc] -> Maybe (Map FName Loc)
buildFieldMap [] [] = Just Map.empty
buildFieldMap (fn:fns) (l:ls) = case buildFieldMap fns ls of
  Just fm -> Just (Map.insert fn l fm)
  Nothing -> Nothing
buildFieldMap [] (_:_) = Nothing
buildFieldMap (_:_) [] = Nothing

-- Constructs a method map from a list of method declarations.
buildMethodMap :: [MDecl] -> Map MName (VName,Expr)
buildMethodMap [] = Map.empty
buildMethodMap (MDecl mn x e:mds) =
  let mm = buildMethodMap mds
  in Map.insert mn (x,e) mm

-- [E1] ★★★
-- Complete the four missing cases of this interpreter for an object oriented
-- programming language.
--
-- Interpret an expressions given a global list of class declarations, a
-- variable environment, and a store.
--
-- interp ∈ list(cdecl) × env × store × expr ⇀ value × store
-- interp(cds,γ,σ,i) ≜ ⟨i,σ⟩
-- interp(cds,γ,σ,e₁+e₂) ≜ ⟨i₁+i₂,σ″⟩
--   where ⟨i₁,σ′⟩ = interp(cds,γ,σ,e₁)
--   where ⟨i₂,σ″⟩ = interp(cds,γ,σ′,e₂)
-- interp(cds,γ,σ,e₁+e₂) ≜ ⟨i₁×i₂,σ″⟩
--   where ⟨i₁,σ′⟩ = interp(cds,γ,σ,e₁)
--   where ⟨i₂,σ″⟩ = interp(cds,γ,σ′,e₂)
-- interp(cds,γ,σ,x) ≜ γ(x)
-- interp(cds,γ,σ,LET x = e₁ IN e₂) ≜ interp(cds,γ[x↦v],σ′,e₂)
--   where ⟨v,σ′⟩ = interp(cds,γ,σ,e₁)
-- interp(cds,γ,σ₀,NEW cn(e₁,…,eₙ)) ≜ ⟨OBJECT cn({fn₁↦ℓ₁,…,fnₘ↦ℓₘ}) {mn₁↦[FUN(x₁)⇒e₁′],…,mnₙ↦[FUN(xₙ)⇒eₙ′]},σₘ[ℓ₁↦v₁,…,ℓₘ↦vₘ]⟩
--   where ⟨v₁,σ₁⟩ = interp(cds,γ,σ₀,e₁)
--                 ⋮
--         ⟨vₘ,σₘ⟩ = interp(cds,γ,σₘ₋₁,eₙ)
--         (CLASS cn FIELDS fn₁ … fnₘ ~ METHOD mn₁(x₁) ⇒ e₁′ … METHOD mnₙ(xₙ) ⇒ eₙ′) = cds(cn)
--         ℓᵢ ≢ ℓⱼ for i ≢ j , 1 ≤ i ≤ m , 1 ≤ j ≤ m
--         {ℓ₁,…,ℓₘ} ∩ dom(σₘ) = ∅
-- interp(cds,γ,σ,e.fn) ≜ ⟨σ(fm(fn)),σ′⟩
--   where ⟨OBJECT cn(fm) mm,σ′⟩ = interp(cds,γ,σ,e)
-- interp(cds,γ,σ,e₁.fn ← e₂) ≜ ⟨v,σ″[fm(fn)↦v]⟩
--   where ⟨OBJECT cn(fm) mm,σ′⟩ = interp(cds,γ,σ,e₁)
--         ⟨v,σ″⟩ = interp(cds,γ,σ′,e₂)
-- interp(cds,γ,e₁.mn(e₂)) ≜ interp(cds,{x↦v,this↦o},σ″,e′)
--   where ⟨o,σ′⟩ = interp(cds,γ,σ,e₁)
--         (OBJECT cn(fm) mm) = o
--         ⟨v,σ″⟩ = interp(cds,γ,σ′,e₂)
--         ⟨x,e′⟩ = mm(mn)
--
-- NOTE: the result of this function is `Maybe (Value,Store)`. This has the same
--       structure of values as the prior `Answer` type:
--
--           data Answer = ValA Value Store | BadA
--
--       if `Maybe (Value,Store)` could be defined directly, it would look like:
--
--           data Maybe (Value,Store) = Just (Value,Store) | Nothing
--
-- HINT: make sure you “thread the store” as in the cases filled out for you,
--       and as in previous assignments.
-- HINT: use `lookupClass` in the case for `NewE` to access the class
--       declaration information for the provided constructor name.
-- HINT: use `interpMany` in the case for `NewE` to interpret each argument to
--       the constructor `es`.
-- HINT: use `allocMany` in the case for `NewE` to simultaneously (1) generate
--       a list of fresh locations in the store, and (2) bind those locations
--       to a list of values (which result from interpreting `es`).
-- HINT: use `buildMethodMap` and `buildFieldMap` in the case for `NewE` to
--       help construct the object to return.
-- HINT: use `Map.lookup` (possibly more than once) in the `GetFieldE` case.
-- HINT: use `Map.lookup` and `Map.insert` in the `SetFieldE` case.
-- HINT: the case for `CallE` should look a lot like a normal function
--       application, but with no closure environment. That is, the final call
--       to interp for the body of the method should always have exactly two
--       entries: one for the formal parameter, and one for the variable
--       "this". You should *not* extend the current environment in this call
--       to interp. (There is one test case to help catch this.)
interp :: [CDecl] -> Env -> Store -> Expr -> Maybe (Value,Store)
interp cds env store e0 = case e0 of
  IntE i -> Just (IntV i,store)
  PlusE e1 e2 -> case interp cds env store e1 of
    Just (IntV i1,store') -> case interp cds env store' e2 of
      Just (IntV i2,store'') -> Just (IntV (i1 + i2),store'')
      _ -> Nothing
    _ -> Nothing
  TimesE e1 e2 -> case interp cds env store e1 of
    Just (IntV i1,store') -> case interp cds env store' e2 of
      Just (IntV i2,store'') -> Just (IntV (i1 * i2),store'')
      _ -> Nothing
    _ -> Nothing
  VarE x -> case Map.lookup x env of
    Just v -> Just (v,store)
    Nothing -> Nothing
  LetE x e1 e2 -> case interp cds env store e1 of
    Just (v,store') -> interp cds (Map.insert x v env) store' e2
    Nothing -> Nothing
  NewE cn es -> error "TODO"
  GetFieldE e fn -> error "TODO"
  SetFieldE e1 fn e2 -> error "TODO"
  CallE e1 mn e2 -> error "TODO"

-- Perform `interp` on a list of expressions.
interpMany :: [CDecl] -> Env -> Store -> [Expr] -> Maybe ([Value],Store)
interpMany cds env store [] = Just ([],store)
interpMany cds env store (e:es) = case interp cds env store e of
  Just (v,store') -> case interpMany cds env store' es of
    Just (vs,store'') -> Just (v:vs,store'')
    Nothing -> Nothing
  Nothing -> Nothing

interpTests :: (Int,String,Expr -> Maybe (Value,Store),[(Expr,Maybe (Value,Store))])
interpTests =
  let cds =
        -- CLASS Point
        --   FIELDS x y
        --   ~
        --   METHOD getX(_) ⇒ this.x
        --   METHOD getY(_) ⇒ this.y
        --   METHOD setX(x) ⇒ this.x ← x
        --   METHOD setY(y) ⇒ this.y ← y
        --   METHOD normsq(_) ⇒ this.getX(0) × this.getX(0) 
        --                    + this.getY(0) × this.getY(0)
        [ CDecl "Point" 
                ["x","y"] 
                [ MDecl "getX" "_" (GetFieldE (VarE "this") "x")
                , MDecl "getY" "_" (GetFieldE (VarE "this") "y")
                , MDecl "setX" "x" (SetFieldE (VarE "this") "x" (VarE "x"))
                , MDecl "setY" "y" (SetFieldE (VarE "this") "y" (VarE "y"))
                , MDecl "normsq" "_" (PlusE (TimesE (CallE (VarE "this") "getX" (IntE 0))
                                                    (CallE (VarE "this") "getX" (IntE 0)))
                                            (TimesE (CallE (VarE "this") "getY" (IntE 0))
                                                    (CallE (VarE "this") "getY" (IntE 0))))
                                           
                                    

                ]
        , CDecl "C"
                ["a","b"]
                [ MDecl "m" "_" (VarE "x") ]
        ]
  in
  (1
  ,"interp"
  ,interp cds Map.empty Map.empty
  -- in each test: interp(e) = ⟨v,σ⟩
  --
  ,[ -- e = LET p = new Point(1,2) IN
     --     p.x
    ( LetE "p" (NewE "Point" [IntE 1,IntE 2]) $
      GetFieldE (VarE "p") "x"
      -- ⟨v,σ⟩ = ⟨1,{0↦1,1↦2}⟩
    , Just (IntV 1,Map.fromList [(0,IntV 1),(1,IntV 2)])
    )
   , -- e = LET p = new Point(1,2) IN
     --     p.getX(0)
    ( LetE "p" (NewE "Point" [IntE 1,IntE 2]) $
      CallE (VarE "p") "getX" (IntE 0)
      -- ⟨v,σ⟩ = ⟨1,{0↦1,1↦2}⟩
    , Just (IntV 1,Map.fromList [(0,IntV 1),(1,IntV 2)])
    )
   , -- e = LET p = new Point(1,2) IN
     --     p.x ← 3 ;
     --     p.getX(0)
    ( LetE "p" (NewE "Point" [IntE 1,IntE 2]) $
      seqE (SetFieldE (VarE "p") "x" (IntE 3)) $
      CallE (VarE "p") "getX" (IntE 0)
      -- ⟨v,σ⟩ = ⟨3,{0↦3,1↦2}⟩
    , Just (IntV 3,Map.fromList [(0,IntV 3),(1,IntV 2)])
    )
   , -- e = LET p = new Point(1,2) IN
     --     p.setX(3) ;
     --     p.x
    ( LetE "p" (NewE "Point" [IntE 1,IntE 2]) $
      seqE (CallE (VarE "p") "setX" (IntE 3)) $
      GetFieldE (VarE "p") "x"
      -- ⟨v,σ⟩ = ⟨3,{0↦3,1↦2}⟩
    , Just (IntV 3,Map.fromList [(0,IntV 3),(1,IntV 2)])
    )
   , -- e = LET p = new Point(0,0) IN
     --     p.setX(3) ;
     --     p.setY(4) ;
     --     p.normsq(0) ;
    ( LetE "p" (NewE "Point" [IntE 0,IntE 0]) $
      seqE (CallE (VarE "p") "setX" (IntE 3)) $
      seqE (CallE (VarE "p") "setY" (IntE 4)) $
      CallE (VarE "p") "normsq" (IntE 0)
      -- v = ⟨25,{0↦3,1↦4}❭
    , Just (IntV 25,Map.fromList [(0,IntV 3),(1,IntV 4)])
    )
   , -- e = LET x = 1 IN
     --     (new C(1,2)).m(0)
     --
     -- (UNDEFINED)
     -- a = Nothing
     ( LetE "x" (IntE 1) $
       CallE (NewE "C" [IntE 1,IntE 2]) "m" (IntE 0)
     , Nothing
     )
   ]
  )

-- [X1]
-- EXTRA CREDIT PROBLEM
--
-- change the language and intepreter to allow for "first class class
-- declarations". That is:
--
-- - class declarations are no long top-level–they can appear in arbitrary
--   sub-expressions
-- - methods are allowed to reference variables which are in scope
-- - the representation of methods inside of objects should close over an
--   environment from when the object was created
-- - calling a method should resume the closure environment, just as was done
--   for first-class functions.
--
-- Here is an example program that should evaluate to 10
--
-- LET z = 3 IN
-- LET Point = CLASS
--               FIELDS x y
--               METHOD thing(w) ⇒ this.x + this.y + z + w
-- IN
-- LET p = new Point(1,2)
-- IN p.md3(4)
--
-- Feel free to copy and re-use any code from above, however make sure you do
-- *not* modify any of the code used in E1.

---------------
-- ALL TESTS --
---------------

allTests :: [Test]
allTests =
  [ Test1 interpTests
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


