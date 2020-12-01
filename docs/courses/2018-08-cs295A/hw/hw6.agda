{-
Name: ⁇
Date: ⁇

Collaboration Statement:
«Write your collaboration statement here…»
-}

---------------
-- LOGISTICS --
---------------

-- To submit the assignment, upload your solution to blackboard as a
-- single .agda file.
--
-- Make sure you write your name, the date, and your collaboration
-- statement above, as indicated by the course course collaboration
-- policy:
--
--     Collaboration on the high-level ideas and approach on
--     assignments is encouraged. Copying someone else's work is not
--     allowed. Any collaboration, even at a high level, must be
--     declared when you submit your assignment. Every assignment must
--     include a collaboration statement. E.g., "I discussed
--     high-level strategies for solving problem 2 and 5 with Alex."
--     Students caught copying work are eligible for immediate failure
--     of the course and disciplinary action by the University. All
--     academic integrity misconduct will be treated according to
--     UVM's Code of Academic Integrity.
--
-- This assignment consists of a LIB section which contains relevant
-- definitions and lemmas which you should refer to throughout the
-- assignment, and an ASSIGNMENT section which contains definitions
-- and lemmas with “holes” in them. *If you only change the code
-- within the holes and your entire assignment compiles without
-- errors, you are guaranteed 100% on the assignment.*

module hw6 where

open import Basics-v2

-- selection sort --

module _ {A : Set} {{_ : has[<?] A}} where

  find-min : A → List A → A ∧ List A
  find-min x [] = ⟨ x , [] ⟩
  find-min x (y ∷ xs) with x ≤? y
  … | LE = let ⟨ m , ys ⟩ = find-min x xs in ⟨ m , y ∷ ys ⟩
  … | GT = let ⟨ m , ys ⟩ = find-min y xs in ⟨ m , x ∷ ys ⟩

  {-# TERMINATING #-}
  ssort : List A → List A
  ssort [] = []
  ssort (x ∷ xs) = let ⟨ m , ys ⟩ = find-min x xs in m ∷ ssort ys

-- list ordering properties --

module _ {A : Set} {{_ : has[<] A}}  where 

  data _≤[List]_ (x : A) : List A → Set where
    [] : x ≤[List] []
    ⟨_⟩ : ∀ {y ys}
      → x ≤ y
      → x ≤[List] (y ∷ ys)
  
  data Sorted : List A → Set where
    [] : Sorted []
    _∷_ : ∀ {x xs}
      → x ≤[List] xs
      → Sorted xs
      → Sorted (x ∷ xs)

  data _⊏[List]_ (x : A) : List A → Set where
    [] : x ⊏[List] []
    _∷_ : ∀ {y ys}
      → x ≤ y
      → x ⊏[List] ys
      → x ⊏[List] (y ∷ ys)

-- proof of sorted-ness for selection sort --

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where 

  -- E1: [★★★]
  -- prove that the min selected from (y ∷ xs) is less than y and less
  -- than everything that wasn't selected.
  -- HINT: do induction on xs
  -- HINT: you will need to do a "link" with pattern:
  --
  --     find-min-lower-bound A B with X ≤? Y | X ≤* Y | X ≤~ Y
  --     … | LE | LE ε | LE = ?
  --     … | GT | GT ε | GT = ?
  --
  -- for some patterns A B and expressions X Y.
  -- HINT: you may need to use ≤-trans
  find-min-lower-bound : ∀ (y : A) (xs : List A) → let ⟨ m , ys ⟩ = find-min y xs in m ≤ y ∧ m ⊏[List] ys
  find-min-lower-bound y xs = {!!}

  -- E2: [★★]
  -- prove that if another value is less than y and less than
  -- everythig in xs, then it is less than the min selected from
  -- (y ∷ xs).
  -- HINT: do induction (you need to figure out on what)
  find-min-upper-bound : ∀ (y z : A) (xs : List A) → z ≤ y → z ⊏[List] xs → let ⟨ m , ys ⟩ = find-min y xs in z ≤ m
  find-min-upper-bound y z [] ε₁ [] = {!!}
  find-min-upper-bound y z (x ∷ xs) ε₁ (ε₂ ∷ εs₂) with y ≤? x
  find-min-upper-bound y z (x ∷ xs) ε₁ (ε₂ ∷ εs₂) | LE with find-min y xs | find-min-upper-bound y z xs ε₁ εs₂
  … | ⟨ m , ys ⟩ | IH = {!find-min-upper-bound y z xs ε₁ εs₂!}
  find-min-upper-bound y z (x ∷ xs) ε₁ (ε₂ ∷ εs₂) | GT = {!!}
  -- find-min-upper-bound y z (x ∷ xs) ε₁ (ε₂ ∷ εs₂) with y ≤? x
  -- … | LE = find-min-upper-bound y z xs ε₁ εs₂
  -- … | GT = {!!}

  -- E3: [★]
  -- prove that if y is less than every element of xs, then y is less
  -- than the sorted version of xs.
  -- HINT: do induction (you need to figure out on what)
  ssort-dom : ∀ (y : A) (xs : List A) → y ⊏[List] xs → y ≤[List] (ssort xs)
  ssort-dom y xs εs = {!!}

  -- E4: [★]
  -- prove that selected sort returns a sorted list.
  -- HINT: do induction (you need to figure out on what)
  {-# TERMINATING #-}
  Sorted[ssort] : ∀ (xs : List A) → Sorted (ssort xs)
  Sorted[ssort] xs = {!!}
