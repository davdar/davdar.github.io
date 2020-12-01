-- [Much of this material is borrowed from [sf.vfa.Selection]
-- authored by Andrew Appel.]
-- 
-- [sf.vfa.Selection]: https://softwarefoundations.cis.upenn.edu/vfa-current/Selection.html

module la12 where

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

  ≤[List]-trans : ∀ (x y : A) (xs : List A) → y ≤[List] xs → x ≤ y → x ≤[List] xs
  ≤[List]-trans x y xs [] ε₂ = []
  ≤[List]-trans x y (x′ ∷ xs) ⟨ ε₁ ⟩ ε₂ = ⟨ ≤-trans x y x′ ε₁ ε₂ ⟩

  ≤[List]-insert : ∀ (x y : A) (xs : List A) → x ≤ y → x ≤[List] xs → x ≤[List] insert y xs
  ≤[List]-insert x y [] ε₁ ε₂ = ⟨ ε₁ ⟩
  ≤[List]-insert x y (z ∷ xs) ε₁ ⟨ ε₂ ⟩ with y ≤? z
  … | LE = ⟨ ε₁ ⟩
  … | GT = ⟨ ε₂ ⟩

  Sorted[insert] : ∀ (x : A) (xs : List A) → Sorted xs → Sorted (insert x xs)
  Sorted[insert] x [] ε = [] ∷ ε
  Sorted[insert] x (y ∷ xs) (ε ∷ εs) with x ≤? y | x ≤* y | x ≤~ y
  … | LE | LE ε′ | LE = ⟨ ε′ ⟩ ∷ (ε ∷ εs)
  … | GT | GT ε′ | GT = ≤[List]-insert y x xs (<-weaken y x ε′) ε ∷ Sorted[insert] x xs εs
  
  Sorted[sort] : ∀ xs → Sorted (isort xs)
  Sorted[sort] [] = []
  Sorted[sort] (x ∷ xs) with Sorted[sort] xs
  … | IH = Sorted[insert] x (isort xs) IH

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
  ssort (x ∷ xs) with find-min x xs
  … | ⟨ m , ys ⟩ = m ∷ ssort ys

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where 

  data _⊏[List]_ (x : A) : List A → Set where
    [] : x ⊏[List] []
    _∷_ : ∀ {y ys}
      → x ≤ y
      → x ⊏[List] ys
      → x ⊏[List] (y ∷ ys)

  find-min-upper-bound-rest : ∀ (y z : A) (xs : List A) → z ≤ y → z ⊏[List] xs → let ⟨ m , ys ⟩ = find-min y xs in z ⊏[List] ys
  find-min-upper-bound-rest y z [] ε [] = []
  find-min-upper-bound-rest y z (x ∷ xs) ε₁ (ε₂ ∷ εs₂) with y ≤? x | y ≤* x | y ≤~ x
  find-min-upper-bound-rest y z (x ∷ xs) ε₁ (ε₂ ∷ εs₂) | LE | LE ε′ | LE with find-min y xs | find-min-upper-bound-rest y z xs ε₁ εs₂
  … | ⟨ m , ys ⟩ | IH = ε₂ ∷ IH
  find-min-upper-bound-rest y z (x ∷ xs) ε₁ (ε₂ ∷ εs₂) | GT | GT ε′ | GT with find-min x xs | find-min-upper-bound-rest x z xs ε₂ εs₂
  … | ⟨ m , ys ⟩ | IH = ε₁ ∷ IH

  postulate
    find-min-lower-bound : ∀ (y : A) (xs : List A) → let ⟨ m , ys ⟩ = find-min y xs in m ≤ y ∧ m ⊏[List] ys
    find-min-upper-bound : ∀ (y z : A) (xs : List A) → z ≤ y → z ⊏[List] xs → let ⟨ m , ys ⟩ = find-min y xs in z ≤ m
    ssort-dom : ∀ (y : A) (xs : List A) → y ⊏[List] xs → y ≤[List] (ssort xs)
    Sorted[ssort] : ∀ (xs : List A) → Sorted (ssort xs)
