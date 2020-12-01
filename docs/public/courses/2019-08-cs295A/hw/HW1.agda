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

module HW1 where

---------
-- LIB --
---------

module Lib where
  infix 4 _≡_

  data _≡_ {A : Set} (x : A) : A → Set where
    ↯ : x ≡ x

  {-# BUILTIN EQUALITY _≡_ #-}

  data 𝔹 : Set where
    True : 𝔹
    False : 𝔹

  data ℕ : Set where
    Z : ℕ
    S : ℕ → ℕ
  
  {-# BUILTIN NATURAL ℕ #-}
  
  _+_ : ℕ → ℕ → ℕ
  Z    + n  =  n
  (S m) + n  =  S (m + n)
  
  data animal : Set where
    Cat : animal
    Dog : animal
    Fish : animal

  is-fuzzy : animal → 𝔹
  is-fuzzy Cat = True
  is-fuzzy Dog = True
  is-fuzzy Fish = False

  is-burpy : animal → 𝔹
  is-burpy Cat = False
  is-burpy Dog = True
  is-burpy Fish = True

  postulate
    would-pet[_] : animal → Set

    would-pet-cat : would-pet[ Cat ]
    would-pet-dog : would-pet[ Dog ]
open Lib public

----------------
-- ASSIGNMENT --
----------------

-- E1: [★☆☆]
-- HINT: do case analysis on `a` then `f[a]`
-- HINT: use `would-pet-cat` and `would-pet-dog`
fuzzy-would-pet : ∀ (a : animal) → is-fuzzy a ≡ True → would-pet[ a ]
fuzzy-would-pet a f[a] = {!!}

-- E2: [★☆☆]
-- HINT: do case analysis on `a`, then `f[a]` and then `b[a]`
dogs-are-fuzzy-and-burpy : ∀ (a : animal) → is-fuzzy a ≡ True → is-burpy a ≡ True → a ≡ Dog
dogs-are-fuzzy-and-burpy a f[a] b[a] = {!!}

-- E3: [★☆☆]
-- HINT: use `↯`
one-plus-one-is-two : 1 + 1 ≡ 2
one-plus-one-is-two = {!!}

-- E4: [★☆☆]
-- HINT: do case analysis (C-c C-c) on the proof of equality `n≡2`
-- HINT: use `↯`
two-plus-two-is-four : ∀ (n : ℕ) → n ≡ 2 → n + 2 ≡ 4
two-plus-two-is-four n n≡2 = {!!}
