-- Lecture Code Notes
module Lc05 where

import Data.Set (Set)
import qualified Data.Set as Set

-----------
-- Lists --
-----------

data IntList = Nil
             | Cons Int IntList
  deriving (Eq,Ord,Show)

-- > singleIntList 1 == Cons 1 Nil
singleIntList :: Int -> IntList
singleIntList x = Cons x Nil

-- > appendIntList (Cons 1 (Cons 2 Nil)) (Cons 3 (Cons 4 Nil)) == Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil)))
appendIntList :: IntList -> IntList -> IntList
appendIntList Nil ys = ys
appendIntList (Cons x xs) ys = Cons x (appendIntList xs ys)

-- > reverseIntList (Cons 1 (Cons 2 Nil)) == Cons 2 (Cons 1 Nil)
reverseIntList :: IntList -> IntList
reverseIntList Nil = Nil
reverseIntList (Cons x xs) = appendIntList (reverseIntList xs) (singleIntList x)

-- > fromIntList e123 == (1:(2:(3:[]))) == (1:2:3:[]) == [1,2,3]
fromIntList :: IntList -> [Int]
fromIntList Nil = []
fromIntList (Cons x xs) = x : fromIntList xs

-- > [1,2,3] +++ [4,5,6] == [1,2,3,4,5,6] == (1:2:3:4:5:6:[])
(+++) :: [a] -> [a] -> [a]
(+++) [] ys = ys
(+++) (x:xs) ys = x:(xs +++ ys)

-- > reverseList [1,2,3] == [3,2,1]
reverseList :: [a] -> [a]
reverseList [] = []
reverseList (x:xs) = reverseList xs +++ [x]

-----------
-- Trees --
-----------

data IntTree = Leaf
             | Node Int IntTree IntTree
  deriving (Eq,Ord,Show)

-- > singleIntTree 1 == Node 1 Leaf Leaf
singleIntTree :: Int -> IntTree
singleIntTree x = Node x Leaf Leaf

-- > treeElements (Node 1 (Node 2 Leaf Leaf) (Node 3 Leaf Leaf)) == [2,1,3]
treeElements :: IntTree -> [Int]
treeElements Leaf = []
treeElements (Node i t1 t2) = treeElements t1 ++ [i] ++ treeElements t2

----------
-- Sets --
----------

-- > {x,y,z}
setE1 :: Set String
setE1 = Set.fromList ["x","y","z"]

-- > {z,y,x}
setE2 :: Set String
setE2 = Set.fromList ["z","x","y"]

-- > {x} ∪ {y} ∪ {z}
setE3 :: Set String
setE3 = Set.union (Set.singleton "x") (Set.union (Set.singleton "y") (Set.singleton "z"))

-- > {x} ∪ {y} ∪ {z}
setE4 :: Set String
setE4 = Set.singleton "x" `Set.union` Set.singleton "y" `Set.union` Set.singleton "z"

-- > {x,y,z,a} ∖ {a}
setE5 :: Set String
setE5 = Set.fromList ["x","y","z","a"] `Set.difference` Set.singleton "a"

-- > {a,x,y,z}
setE6 :: Set String
setE6 = Set.fromList ["x","y","z","a"]

-- > x ∈ {x,y,z}
setT1 :: Bool
setT1 = Set.member "x" setE1

-- > {x,y,z} ⊆ {x,y,z}
setT2 :: Bool
setT2 = Set.isSubsetOf setE5 setE5

-- > {x,y,z} ⊆ {a,x,y,z}
setT3 :: Bool
setT3 = Set.isSubsetOf setE5 setE6

-- > {a,x,y,z} ⊆ {x,y,z}
setT4 :: Bool
setT4 = Set.isSubsetOf setE6 setE5
