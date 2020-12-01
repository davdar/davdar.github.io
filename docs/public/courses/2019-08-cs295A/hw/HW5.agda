{-
Name: ⁇
Date: ⁇

Collaboration & Resources Statement:
«Write your statement here…»
-}

---------------
-- LOGISTICS --
---------------

-- To submit the assignment, upload your solution to Gradescope as a
-- single .agda file.
--
-- Make sure you write your name, the date, and your collaboration
-- & Resources statement above, as indicated by the course
-- collaboration and resources policy:
--
--     Collaboration on the high-level ideas and approach on assignments
--     is encouraged. Copying someone else's work is not allowed. Copying
--     solutions from an online source is not allowed. Any collaboration
--     or online resources, even if used only at a high level, must be
--     declared when you submit your assignment. Every assignment must
--     include a collaboration and resources statement. E.g., “I discussed
--     high-level strategies for solving problem 2 and 5 with Alex; I
--     found this stackoverflow post helpful while working on problem 3 ”
--     Students caught copying work are eligible for immediate failure of
--     the course and disciplinary action by the University. All academic
--     integrity misconduct will be treated according to UVM's Code of
--     Academic Integrity.
--
-- This assignment consists of a LIB section which contains relevant
-- definitions and lemmas which you should refer to throughout the
-- assignment, and an ASSIGNMENT section which contains definitions
-- and lemmas with “holes” in them. *If you only change the code
-- within the holes and your entire assignment compiles without
-- errors, you are guaranteed 100% on the assignment.*

module HW5 where

---------
-- LIB --
---------

-- equality --

infix 8 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

-- naturals --

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 15 _+_
_+_ : ℕ → ℕ → ℕ
Z    + n  =  n
(S m) + n  =  S (m + n)

infixl 16 _×_
_×_ : ℕ → ℕ → ℕ
Z × _ = Z
S m × n = n + m × n

-- lists --

infixr 20 _∷_
data list (A : Set) : Set where
  [] : list A
  _∷_ : A → list A → list A

pattern [_] a = a ∷ []
pattern [_,_] a b = a ∷ [ b ]
pattern [_,_,_] a b c = a ∷ [ b , c ]
pattern [_,_,_,_] a b c d = a ∷ [ b , c , d ]
pattern [_,_,_,_,_] a b c d e = a ∷ [ b , c , d , e ]
pattern [_,_,_,_,_,_] a b c d e f = a ∷ [ b , c , d , e , f ]
pattern [_,_,_,_,_,_,_] a b c d e f g = a ∷ [ b , c , d , e , f , g ]
pattern [_,_,_,_,_,_,_,_] a b c d e f g h = a ∷ [ b , c , d , e , f , g , h ]
pattern [_,_,_,_,_,_,_,_,_] a b c d e f g h i = a ∷ [ b , c , d , e , f , g , h , i ]
pattern [_,_,_,_,_,_,_,_,_,_] a b c d e f g h i j = a ∷ [ b , c , d , e , f , g , h , i , j ]

_ : list ℕ
_ = [ 1 ]

_ : list ℕ
_ = 1 ∷ []


infixl 16 _⧺_
_⧺_ : ∀ {A : Set} → list A → list A → list A
[] ⧺ ys = ys
(x ∷ xs) ⧺ ys = x ∷ (xs ⧺ ys)

reverse : ∀ {A : Set} → list A → list A
reverse [] = []
reverse (x ∷ xs) = reverse xs ⧺ [ x ]

map : ∀ {A B : Set} → (A → B) → list A → list B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- functions -- 

id : ∀ {A : Set} → A → A
id x = x

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- POSTULATES --

postulate
  reduc[+] : ∀ (m n : ℕ) → m + S n ≡ S (m + n)
  runit[+] : ∀ (m : ℕ) → m + 0 ≡ m
  assoc[+] : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
  commu[+] : ∀ (m n : ℕ) → m + n ≡ n + m

  runit[×] : ∀ (m : ℕ) → m × 1 ≡ m
  rzero[×] : ∀ (m : ℕ) → m × 0 ≡ 0
  assoc[×] : ∀ (m n p : ℕ) → m × (n × p) ≡ (m × n) × p
  commu[×] : ∀ (m n : ℕ) → m × n ≡ n × m
  ldist[×] : ∀ (m n p : ℕ) → m × (n + p) ≡ m × n + m × p
  rdist[×] : ∀ (m n p : ℕ) → (m + n) × p ≡ m × p + n × p

  runit[⧺] : ∀ {A} (xs : list A) → xs ⧺ [] ≡ xs
  assoc[⧺] : ∀ {A} (xs ys zs : list A) → xs ⧺ (ys ⧺ zs) ≡ (xs ⧺ ys) ⧺ zs

----------------
-- ASSIGNMENT --
----------------

-- E1: [★★☆]
-- Prove that if you reverse the concatenation of two lists, it's the
-- same as concatenating the reversal of each list (in reverse order).
-- This is a homomorphic property for reverse composed with
-- concatenation.
-- HINTS:
-- ‣ do induction
-- ‣ use lemmas about ⧺ postulated above
homom[reverse/⧺] : ∀ {A : Set} (xs ys : list A) → reverse (xs ⧺ ys) ≡ reverse ys ⧺ reverse xs
homom[reverse/⧺] [] ys rewrite runit[⧺] (reverse ys) = ↯
homom[reverse/⧺] (x ∷ xs) ys = {!!}

-- E2: [★★☆]
-- Prove that if you reverse a list twice, you get the list you
-- started with. This is an involutave property for reverse.
-- HINTS:
-- ‣ do induction
-- ‣ use lemmas about ⧺ postulated above
-- ‣ use result of previous exercise
invol[reverse] : ∀ {A : Set} (xs : list A) → reverse (reverse xs) ≡ xs
invol[reverse] [] = ↯
invol[reverse] (x ∷ xs) = {!!}

-- E3: [★☆☆]
-- Prove that if you map the identity function, it's the same as the
-- identity function. This is a unit property for map.
-- HINTS:
-- ‣ do induction
unit[map] : ∀ {A : Set} (xs : list A) → map id xs ≡ xs
unit[map] xs = {!!}

-- E4: [★★☆]
-- Prove that if you map the composition of functions, it is the same
-- as composing the map of those functions. This is a homomorphic
-- property for map composed with compose.
-- HINTS:
-- ‣ do induction
homom[map/∘] : ∀ {A B C : Set} (g : B → C) (f : A → B) (xs : list A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
homom[map/∘] g f xs = {!!}

-- E5: [★★☆]
-- Prove that if you map onto the concatenation of lists, it's the
-- same as the concatenation of mapped lists. This is a homomorhpic
-- property for map composed with concatenation.
-- HINTS:
-- ‣ do induction
homom[map/⧺] : ∀ {A B : Set} (f : A → B) (xs ys : list A) → map f (xs ⧺ ys) ≡ map f xs ⧺ map f ys
homom[map/⧺] f xs ys = {!!}

-- E6: [★★★]
-- Prove that if you map after you reverse, this is the same as
-- reversing after a map. This is a commutative property between map
-- and reverse.
-- HINTS:
-- ‣ do induction
-- ‣ use any of the lemmas postulated above, and/or any previous
--   exercise
commu[map/reverse] : ∀ {A B : Set} (f : A → B) (xs : list A) → map f (reverse xs) ≡ reverse (map f xs)
commu[map/reverse] f xs = {!!}

-- E7: [★☆☆]
-- Define a function which sums up all of the elements of a list.
sum : list ℕ → ℕ
sum xs = {!!}

_ : sum [] ≡ 0
_ = ↯

_ : sum [ 1 ] ≡ 1
_ = ↯

_ : sum [ 1 , 2 ] ≡ 3
_ = ↯

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ = ↯

_ : sum [ 4 , 3 , 2 , 1 ] ≡ 10
_ = ↯

-- E8: [★★☆]
-- prove that the sum of the concatenation of two lists is the sum of
-- sum of the two lists. This is a homomorphic property for sum
-- composed with concatenation.
-- list.
-- HINTS:
-- ‣ do induction
-- ‣ use any of the lemmas postulated above, and/or any previous
--   exercise
homom[sum/⧺] : ∀ (xs ys : list ℕ) → sum (xs ⧺ ys) ≡ sum xs + sum ys
homom[sum/⧺] xs ys = {!!}

-- EXTRA PROBLEMS (not graded)
--
-- 1. prove that (sum (reverse xs)) ≡ sum xs
-- 2. define:
-- 
--        singleton  : A → list A
--        concat-map : list A → (A → list B) → list B
--         
--    (you just implemented the list monad, provided that (3) (the next problem) is provable)
--
-- 3. prove:
--
--        concat-map (singleton x) f ≡ f x
--        concat-map xs singleton ≡ xs
--        concat-map (concat-map xs f) g ≡ concat-map xs (λ x → concat-map (f x) g)
--
--    (you just proved the monad laws for your implementation of the list monad)
--
-- 4. define transpose on lists of lists, so
--
--        transpose [ [ 1 , 2 ]
--                  , [ 3 , 4 ]
--                  , [ 5 , 6 ]
--                  ]
--        ≡
--        [ [ 1 , 3 , 5 ]
--        , [ 2 , 4 , 6 ]
--        ]
--
-- 5. prove that (transpose (transpose xs)) ≡ xs
