module ic14 where

open import Basics-v2

--------------
-- IN CLASS --
--------------

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

-- merge sort --

module _ {A : Set} {{_ : has[<?] A}} where

  split : A → A → List A → List A ∧ List A
  split w x [] = ⟨ [ w ] , [ x ] ⟩
  split w x [ y ] = ⟨ [ w , x ] , [ y ] ⟩
  split w x (y ∷ z ∷ xs) = let ⟨ ys , zs ⟩ = split y z xs in ⟨ w ∷ ys , x ∷ zs ⟩

  postulate
    split-length : ∀ (x y : A) (xs : List A) → let ⟨ ys , zs ⟩ = split x y xs in length ys < length (x ∷ y ∷ xs) ∧ length zs < length (x ∷ y ∷ xs)

  merge : List A → List A → List A
  merge [] ys = ys
  merge xs [] = xs
  merge (x ∷ xs) (y ∷ ys) with x ≤? y
  … | LE = x ∷ merge xs (y ∷ ys)
  … | GT = y ∷ merge (x ∷ xs) ys

  {-# TERMINATING #-}
  msort : List A → List A
  msort [] = []
  msort [ x ] = [ x ]
  msort (x ∷ y ∷ xs) = let ⟨ ys , zs ⟩ = split x y xs in merge (msort ys) (msort zs)

-- well founded relations --

data Acc {A : Set} (_≺_ : A → A → Set) (x : A) : Set where
  acc : (∀ {y} → y ≺ x → Acc _≺_ y) → Acc _≺_ x

WF : ∀ {A : Set} → (A → A → Set) → Set
WF _≺_ = ∀ x → Acc _≺_ x

<ᴺ-wf′ : ∀ {m} (n : ℕ) → m < n → Acc _<_ m
<ᴺ-wf′ (suc n) zero = acc (λ where ())
<ᴺ-wf′ (suc n) (suc ε) = acc (λ ε′ → <ᴺ-wf′ n (<-trans-l _ _ n (≤-fr-< ε′) ε))

<ᴺ-wf : ∀ (n : ℕ) → Acc _<_ n
<ᴺ-wf n = acc (λ ε → <ᴺ-wf′ n ε)

module _ {A : Set} {{_ : has[<] A}} {{_ : has[<?] A}} where

  msort′ : ∀ (xs : List A) → Acc _<_ (length xs) → List A
  msort′ [] ε = []
  msort′ [ x ] ε = [ x ]
  msort′ (x ∷ y ∷ xs) (acc r) =
    let ⟨ ys , zs ⟩ = split x y xs
        ⟨ H₁ , H₂ ⟩ = split-length x y xs
    in merge (msort′ ys (r H₁)) (msort′ zs (r H₂))

  msort′-t : List A → List A
  msort′-t xs = msort′ xs (<ᴺ-wf (length xs))

  msort″ : ∀ (xs : List A) → (∀ (ys : List A) → length ys < length xs → List A) → List A
  msort″ xs rec = {!!}

  msort″-t : List A → List A
  msort″-t xs = {!!}
    where
      f : ∀ (xs : List A) → Acc _<_ (length xs) → List A
      f xs ε = {!!}

_ : msort′-t [ 3 , 2 , 4 , 1 ] ≡ [ 1 , 2 , 3 , 4 ]
_ = {!!}
