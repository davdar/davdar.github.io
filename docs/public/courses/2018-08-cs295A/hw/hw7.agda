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

module hw7 where

open import Basics-v2

-- sorted specification --

module _ {A : Set} {{_ : has[<] A}} where

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

-- accessibility and well founded --

data Acc {A : Set} (_≺_ : A → A → Set) (x : A) : Set where
  acc : (∀ {y} → y ≺ x → Acc _≺_ y) → Acc _≺_ x

WF : ∀ {A : Set} → (A → A → Set) → Set
WF _≺_ = ∀ x → Acc _≺_ x

<ᴺ-wf′ : ∀ {m} (n : ℕ) → m < n → Acc _<_ m
<ᴺ-wf′ zero ()
<ᴺ-wf′ (suc n) zero = acc λ where ()
<ᴺ-wf′ (suc n) (suc ε) = acc λ where ε′ → (<ᴺ-wf′ n) (<-trans-l _ _ n (≤-fr-< ε′) ε)

<ᴺ-wf : ∀ (n : ℕ) → Acc _<_ n
<ᴺ-wf n = acc (<ᴺ-wf′ n)

-- merge sort --

module _ {A : Set} {{_ : has[<?] A}} where

  split : A → A → List A → List A ∧ List A
  split w x [] = ⟨ [ w ] , [ x ] ⟩
  split w x [ y ] = ⟨ [ w , x ] , [ y ] ⟩
  split w x (y ∷ z ∷ xs) = let ⟨ ys , zs ⟩ = split y z xs in ⟨ w ∷ ys , x ∷ zs ⟩

  -- E1: [★★]
  -- Prove that if you split a list, the resulting lists are strictly
  -- smaller than the starting list.
  -- HINT: use <ᴺ-lmono
  split-length : ∀ (x y : A) (xs : List A) → let ⟨ ys , zs ⟩ = split x y xs in length ys < length (x ∷ y ∷ xs) ∧ length zs < length (x ∷ y ∷ xs)
  split-length x y xs = {!!}

  merge : List A → List A → List A
  merge [] ys = ys
  merge xs [] = xs
  merge (x ∷ xs) (y ∷ ys) with x ≤? y
  … | LE = x ∷ merge xs (y ∷ ys)
  … | GT = y ∷ merge (x ∷ xs) ys

  msort′ : ∀ (xs : List A) → Acc _<_ (length xs) → List A
  msort′ [] ε = []
  msort′ [ x ] ε = [ x ]
  msort′ (x ∷ y ∷ xs) (acc r) =
    let ⟨ ys , zs ⟩ = split x y xs
        ⟨ H₁ , H₂ ⟩ = split-length x y xs
    in merge (msort′ ys (r H₁)) (msort′ zs (r H₂))

  msort : List A → List A
  msort xs = msort′ xs (<ᴺ-wf (length xs))

-- verification of merge sort --

module _ {A : Set} {{_ : has[<?] A}} {{_ : has[<] A}} {{_ : cor[<?] A}} {{_ : cor[<] A}} where

  -- E2: [★]
  -- Prove that if x is smaller than the head of xs and ys, then x is
  -- smaller than the merge of xs and ys.
  merge-bounded : ∀ (x : A) (xs ys : List A) → x ≤[List] xs → x ≤[List] ys → x ≤[List] (merge xs ys)
  merge-bounded x xs ys ε₁ ε₂ = {!!}

  -- E3: [★★]
  -- Prove that if xs is sorted and ys is sorted, then the merge is
  -- sorted.
  merge-sorted : ∀ (xs ys : List A) → Sorted xs → Sorted ys → Sorted (merge xs ys)
  merge-sorted xs ys ε₁ ε₂ = {!!}

  -- E4: [★★★]
  -- Prove that the recursively defined version of merge sort results
  -- in a sorted list
  msort′-sorted : ∀ (xs : List A) (ε : Acc _<_ (length xs)) → Sorted (msort′ xs ε)
  msort′-sorted [] ε = {!!}
  msort′-sorted [ x ] ε = {!!}
  msort′-sorted (x ∷ y ∷ xs) (acc ε) with split x y xs | split-length x y xs
  … | ⟨ ys , zs ⟩ | ⟨ H₁ , H₂ ⟩ =
    ?
    -- let IH₁ = msort′-sorted ys (ε H₁)
    --     IH₂ = msort′-sorted zs (ε H₂)
    -- in merge-sorted (msort′ ys (ε H₁)) (msort′ zs (ε H₂)) IH₁ IH₂

  -- E5: [★]
  -- Prove that merge sort results in a sorted list
  -- HINT: use <ᴺ-wf
  msort-sorted : ∀ (xs : List A) → Sorted (msort xs)
  msort-sorted xs = {!!}
