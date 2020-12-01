-- [Much of this material is borrowed from [sf.vfa.Selection]
-- authored by Andrew Appel.]
-- 
-- [sf.vfa.Selection]: https://softwarefoundations.cis.upenn.edu/vfa-current/Selection.html

module ic12 where

open import Basics-v1

--------------
-- IN CLASS --
--------------

-- insertion sort --

module _ {A : Set} {{_ : has[<?] A}} where

  insert : A → List A → List A
  insert x [] = x ∷ []
  insert x (y ∷ ys) with x ≤? y
  … | LE = x ∷ y ∷ ys
  … | GT = y ∷ insert x ys
  
  isort : List A → List A
  isort [] = []
  isort (x ∷ xs) = insert x (isort xs)

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

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where 

  ≤[List]-trans : ∀ (y z : A) (xs : List A) → z ≤[List] xs → y ≤ z → y ≤[List] xs
  ≤[List]-trans y z xs ε₁ ε₂ = {!!}

  ≤[List]-insert : ∀ (y z : A) (xs : List A) → y ≤ z → y ≤[List] xs → y ≤[List] insert z xs
  ≤[List]-insert y z xs ε₁ ε₂ = {!!}

  Sorted[insert] : ∀ (y : A) (xs : List A) → Sorted xs → Sorted (insert y xs)
  Sorted[insert] y xs εs = {!!}
  
  Sorted[sort] : ∀ (xs : List A) → Sorted (isort xs)
  Sorted[sort] xs = {!!}

-- selection sort --

module _ {A : Set} {{_ : has[<?] A}} where

  find-min : A → List A → A ∧ List A
  find-min y xs = {!!}

  ssort : List A → List A
  ssort xs = {!!}

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where 

  data _⊏[List]_ (x : A) : List A → Set where
    [] : x ⊏[List] []
    _∷_ : ∀ {y ys}
      → x ≤ y
      → x ⊏[List] ys
      → x ⊏[List] (y ∷ ys)

  find-min-upper-bound-rest : ∀ (y z : A) (xs : List A) → z ≤ y → z ⊏[List] xs → let ⟨ m , ys ⟩ = find-min y xs in z ⊏[List] ys
  find-min-upper-bound-rest y z xs ε εs = {!!}

  postulate
    find-min-lower-bound : ∀ (y : A) (xs : List A) → let ⟨ m , ys ⟩ = find-min y xs in m ≤ y ∧ m ⊏[List] ys
    find-min-upper-bound : ∀ (y z : A) (xs : List A) → z ≤ y → z ⊏[List] xs → let ⟨ m , ys ⟩ = find-min y xs in z ≤ m
    ssort-dom : ∀ (y : A) (xs : List A) → y ⊏[List] xs → y ≤[List] (ssort xs)
    Sorted[ssort] : ∀ (xs : List A) → Sorted (ssort xs)
