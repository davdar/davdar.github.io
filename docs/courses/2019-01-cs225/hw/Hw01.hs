{-# LANGUAGE GADTs #-} -- used in testing infrastructure
module Hw01 where

{-

HW1 v1.1

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

-- For your reference, here are two functions written in Haskell.

-- Here is the factorial function in Haskell.
-- E.g.:
--
--     factorial 4
--     ==
--     4 * 3 * 2 * 1 * 1
--     ==
--     24
--
factorial :: Int -> Int
factorial n
  | n <= 0    = 1
  | otherwise = n * factorial (n - 1)

-- Here is a function that drops a common prefix between two lists.
-- E.g.:
--
--     dropCommonPrefix [1,2,3,4,5,6] [1,2,3,11,22,33]
--     ==
--     ([4,5,6],[11,22,33])
--
dropCommonPrefix :: [Int] -> [Int] -> ([Int],[Int])
dropCommonPrefix [] [] = ([],[])
dropCommonPrefix [] (y:ys) = ([],y:ys)
dropCommonPrefix (x:xs) [] = (x:xs,[])
dropCommonPrefix (x:xs) (y:ys)
  | x == y    = dropCommonPrefix xs ys
  | otherwise = (x:xs,y:ys)

-- [E1]
-- Take two arguments as input `x` and `y` and return `x * (x + y)`
-- E.g.:
--
--     timesAfterPlus 4 5
--     ==
--     4 * (4 + 5)
--     ==
--     4 * 9
--     ==
--     36
--
timesAfterPlus :: Int -> Int -> Int
timesAfterPlus x y = error "TODO"

timesAfterPlusTests :: (Int,String,Int -> Int -> Int,[((Int,Int),Int)])
timesAfterPlusTests =
  ( 1
  , "timesAfterPlus"
  , timesAfterPlus
  , [((4,5),36)
    ,((3,4),21)
    ]
  )


-- [E2]
-- Countdown
-- Take one argument as input `x` and return a string which is all of the
-- numbers between `x` and `0`, inclusive. If the input is negative, throw an
-- error. (This part is written for you.)
-- E.g.:
--
--     countdown 11
--     ==
--     "11109876543210"
--
-- HINT: the concatenation function for lists is `list1 ++ list2`
-- HINT: the function which turns an Int into a String is `show`
-- HINT: define the function recursively:
--
--     countdown x
--       -- bad input
--       | x < 0 = ...
--       -- the base case
--       | x == 0 = ...
--       -- the recursive case
--       | otherwise = ... countdown (x - 1) ...
--
countdown :: Int -> String
countdown x
  | x < 0 = error "countdown: negative input"
  | otherwise = error "TODO"

countdownTests :: (Int,String,Int -> String,[(Int,String)])
countdownTests =
  ( 2
  , "countdown"
  , countdown
  , [(11,"11109876543210")
    ,(10,"109876543210")
    ]
  )

-- [E3]
-- Convert a list of fruit---represented as strings--where apples are converted
-- into oranges, and oranges are converted into bananas
-- E.g.:
--
--     convertFruitString
--     ["apple", "banana", "orange", "kiwi"]
--     ==
--     ["orange", "banana", "banana", "kiwi"]
--
-- HINT: the operator to compare if two strings are equal or not is `string1 ==
-- string2`, which returns a boolean (something of type `Bool`).
--
-- HINT: the syntax for conditional statements is `if ... then ... else ...`.
-- Note that in Haskell whitespace is relevant to parse program structure. If
-- you put `then` and `else` on new lines, they should indent like this:
--
--     if <some stuff>
--     then <more stuff>
--          <still inside the then branch>
--     else <more stuff>
--          <still inside the else branch>
--
-- or this:
--
--     if
--       <some stuff>
--     then
--       <more stuff>
--       <still inside the then branch>
--     else
--       <more stuff>
--       <still inside the else branch>
--
-- HINT: define the function recursively, and by pattern matching on the input
-- `fruits`, i.e.:
--
--     convertFruitString [] = ...
--     convertFruitString (fruit:fruits) = ...
--
-- In the second line, `fruit` will be an element of the list (a string) and
-- `fruits` will be the rest of the list (a list of strings). In the second
-- line (called the recursive case), you should call `convertFruitString` on
-- `fruits`.
convertFruitString :: [String] -> [String]
convertFruitString fruits = error "TODO"

convertFruitStringTests :: (Int,String,[String] -> [String],[([String],[String])])
convertFruitStringTests =
  ( 3
  , "convertFruitString"
  , convertFruitString
  , [(["apple", "banana", "orange", "kiwi"],["orange", "banana", "banana", "kiwi"])
    ,(["pineapple","orange","banana","apple"],["pineapple","banana","banana","orange"])
    ]
  )


-- [E4]
-- This is a datatype that enumerates a fixed set of possible fruit. This is
-- similar to Java's enum types. The `data` keyword is technically creating an
-- "Algebraic Datatype" which is much more powerful than a simple enumeration
-- (as is Java's enum)
data Fruit =
    Apple
  | Banana
  | Blackberry
  | Blueberry
  | Cantaloupe
  | Cherry
  | Grapefruit
  | Kiwi
  | Lemon
  | Mango
  | Orange
  | Papaya
  | Pear
  | Pineapple
  | Raspberry
  | Starfruit
  | Strawberry
  | Watermelon
  deriving (Eq,Ord,Show)

-- Convert a list of fruit---represented as strings--where apples are converted
-- into oranges, and oranges are converted into bananas
-- e.g.:
--
--     convertFruitEnum [Apple, Banana, Orange, Kiwi] == [Orange, Banana, Banana, Kiwi]
--
convertFruitEnum :: [Fruit] -> [Fruit]
convertFruitEnum fruits = error "TODO"

convertFruitEnumTests :: (Int,String,[Fruit] -> [Fruit],[([Fruit],[Fruit])])
convertFruitEnumTests =
  ( 4
  , "convertFruitEnum"
  , convertFruitEnum
  , [([Apple,Banana,Orange,Kiwi],[Orange,Banana,Banana,Kiwi])
    ,([Pineapple,Orange,Banana,Apple],[Pineapple,Banana,Banana,Orange])
    ]
  )

----------------------
-- MAIN = RUN TESTS --
----------------------

main :: IO ()
main = runTests
  [ Test2 timesAfterPlusTests
  , Test1 countdownTests
  , Test1 convertFruitStringTests
  , Test1 convertFruitEnumTests
  ]

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
