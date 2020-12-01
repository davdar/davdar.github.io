module la13 where

open import Basics-v1

--------------
-- IN CLASS --
--------------

module LastTime {A : Set} {{_ : has[<?] A}} where

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

-- selection sort --

module _ {A : Set} {{_ : has[<?] A}} where

  find-min : A → List A → A ∧ List A
  find-min x [] = ⟨ x , [] ⟩
  find-min x (y ∷ xs) with x ≤? y
  … | LE = let ⟨ m , ys ⟩ = find-min x xs in ⟨ m , y ∷ ys ⟩
  … | GT = let ⟨ m , ys ⟩ = find-min y xs in ⟨ m , x ∷ ys ⟩

  find-min-length : ∀ (y : A) (xs : List A) → let ⟨ m , xs′ ⟩ = find-min y xs in length xs ≡ length xs′
  find-min-length y [] = refl
  find-min-length y (x ∷ xs) with y ≤? x
  … | LE rewrite find-min-length y xs = refl
  … | GT rewrite find-min-length x xs = refl

  ssort : ∀ (n : ℕ) (xs : List A) → length xs ≡ n → List A
  ssort 0 [] refl = []
  ssort zero (x ∷ xs) ()
  ssort (suc n) [] ()
  ssort (suc n) (x ∷ xs) ε with find-min x xs | length xs | find-min-length x xs
  … | ⟨ m , ys ⟩ | lxs | ε′ rewrite ε′ with ssort n ys | ε
  … | IH | refl = m ∷ IH refl

-- static length index --

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero 
  _∷_ : ∀ {n : ℕ} → A → Vec A n → Vec A (suc n)

_++ⱽ_ : ∀ {m n : ℕ} {A : Set} → Vec A m → Vec A n → Vec A (m + n)
[] ++ⱽ ys = ys
(x ∷ xs) ++ⱽ ys = x ∷ (xs ++ⱽ ys)

reverseⱽ : ∀ {m : ℕ} {A : Set} → Vec A m → Vec A m
reverseⱽ [] = []
reverseⱽ {m = suc m} (x ∷ xs) with reverseⱽ xs ++ⱽ (x ∷ [])
… | xs′ rewrite +-commu m 1 = xs′

module _ {A : Set} {{_ : has[<?] A}} where
  find-min′ : ∀ {n} → A → Vec A n → A ∧ Vec A n
  find-min′ x [] = ⟨ x , [] ⟩
  find-min′ x (y ∷ xs) with x ≤? y
  … | LE = let ⟨ m , ys ⟩ = find-min′ x xs in ⟨ m , y ∷ ys ⟩
  … | GT = let ⟨ m , ys ⟩ = find-min′ y xs in ⟨ m , x ∷ ys ⟩

  ssort′ : ∀ {n : ℕ} (xs : Vec A n) → Vec A n
  ssort′ {zero} [] = []
  ssort′ {suc n} (x ∷ xs) = let ⟨ m , ys ⟩ = find-min′ x xs in m ∷ ssort′ {n = n} ys

-- intrinsic verification --

data Option (A : Set) : Set where
  None : Option A
  Some : A → Option A

module _ {A : Set} {{_ : has[<] A}} where
  data _≤[Option]_ (x : A) : Option A → Set where
    None : x ≤[Option] None
    some : ∀ {y} → x ≤ y → x ≤[Option] Some y

data SortedVec (A : Set) {{_ : has[<] A}} : ℕ → Option A → Set where
  [] : SortedVec A zero None
  cons : ∀ {n yO}
    → (x : A)
    → (xs : SortedVec A n yO)
    → x ≤[Option] yO
    → SortedVec A (suc n) (Some x)

-- helpers --

<ᴺ-rmono : ∀ (m n p : ℕ) → m < n → m < n + p
<ᴺ-rmono _ _ p zero = zero
<ᴺ-rmono _ _ p (suc ε) = suc (<ᴺ-rmono _ _ p ε)

<ᴺ-lmono : ∀ (m n p : ℕ) → m < p → m < n + p
<ᴺ-lmono m n p ε rewrite +-commu n p = <ᴺ-rmono m p n ε

-- merge sort --

module _ {A : Set} {{_ : has[<?] A}} where

  split : A → List A → List A ∧ List A
  split x [] = ⟨ [] , [] ⟩
  split x [ y ] = ⟨ [ x ] , [ y ] ⟩
  split x (y ∷ z ∷ xs) = let ⟨ ys , zs ⟩ = split z xs in ⟨ x ∷ ys , y ∷ zs ⟩

  postulate
    split-length : ∀ (x : A) (xs : List A) → let ⟨ ys , zs ⟩ = split x xs in length ys < suc (length xs) ∧ length zs < suc (length xs)

  merge : List A → List A → List A
  merge [] ys = ys
  merge xs [] = xs
  merge (x ∷ xs) (y ∷ ys) with x ≤? y
  … | LE = x ∷ merge xs (y ∷ ys)
  … | GT = y ∷ merge (x ∷ xs) ys

  {-# TERMINATING #-}
  msort : List A → List A
  msort [] = []
  msort (x ∷ xs) = let ⟨ ys , zs ⟩ = split x xs in merge (msort ys) (msort zs)

