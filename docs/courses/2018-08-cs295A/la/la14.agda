module la14 where

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
    split-length : ∀ (x y : A) (xs : List A) → let ⟨ ys , zs ⟩ = split x y xs
                                               in length ys < length (x ∷ y ∷ xs)
                                                ∧ length zs < length (x ∷ y ∷ xs)

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

-- _<_ is *well-founded* if for every (n : ℕ), _<_ is *accessible* on n
-- WF _<_ ≜ ∀ (n : ℕ) → Acc _<_ n
--
-- _<_ is *accessible* on n if for every m < n, m is accessible on _<_
-- Acc _<_ n ≜ ∀ m → m < n → Acc _<_ m

-- e.g.,
-- _<_ is accessible on 0
-- why: ∀ m → m < 0 → _<_ is accessible on m
-- why: ∀ m → m < 0 → ANYTHING

-- _<_ is accessible on 1
-- why: ∀ m → m < 1 → Acc _<_ m
-- b.c.: _<_ accessible on 0

-- _<_ is accessible on 2
-- why: ∀ m → m < n → Acc _<_ m
-- b.c.: _<_ accessible on 0 and 1

-- accessibility means that if you keep chaining the relation,
-- eventually you will come up with evidence that is absurd.

-- accessibility means that there are a finite number of things
-- related to the root

-- accessibility means that you can do induction justified by the
-- custom relation, as opposed to Agda's syntactic equality check

-- strategy:
-- (1) want to define `msort : List A → List A`
-- (2) instead define `msort : ∀ (xs : List A) → Acc _<_ (length xs) → List A
-- (3) notice that `∀ (n : ℕ) → Acc _<_ n`
-- (4) instantiate (2) with a proof of `Acc _<_ (length xs)` (always
--     possible because (3))

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

module _ {A : Set} {{_ : has[<] A}} {{_ : has[<?] A}} where

  msort′ : ∀ (xs : List A) → Acc _<_ (length xs) → List A
  msort′ [] (acc r) = []
  msort′ [ x ] (acc r) = [ x ]
  msort′ (x ∷ y ∷ xs) (acc r) =
    let ⟨ ys , zs ⟩ = split x y xs
        ⟨ H₁ , H₂ ⟩ = split-length x y xs
    in merge (msort′ ys (r H₁)) (msort′ zs (r H₂))

  msort′-t : List A → List A
  msort′-t xs = msort′ xs (<ᴺ-wf (length xs))

  msort″ : ∀ (xs : List A) → (∀ (ys : List A) → length ys < length xs → List A) → List A
  msort″ [] rec = []
  msort″ [ x ] rec = [ x ]
  msort″ (x ∷ y ∷ xs) rec =
    let ⟨ ys , zs ⟩ = split x y xs
        ⟨ H₁ , H₂ ⟩ = split-length x y xs
    in merge (rec ys H₁) (rec zs H₂)

  msort″-t : List A → List A
  msort″-t xs = f xs (<ᴺ-wf (length xs))
    where
      f : ∀ (xs : List A) → Acc _<_ (length xs) → List A
      f xs (acc r) = msort″ xs (λ ys ε → f ys (r ε))

  msort-fuel : ℕ → List A → Option (List A)
  msort-fuel zero _ = None
  msort-fuel (suc n) [] = Some []
  msort-fuel (suc n) [ x ] = Some [ x ]
  msort-fuel (suc n) (x ∷ y ∷ xs) =
    let ⟨ ys , zs ⟩ = split x y xs
    in CASE msort-fuel n ys OF λ where
      None → None
      (Some ys′) → CASE msort-fuel n zs OF λ where
        None → None
        (Some zs′) → Some (merge ys′ zs′)

  -- terminates : ∀ (xs : List A) → ∃ ys ⦂ List A 𝑠𝑡 msort-fuel ? xs ≡ Some ys
  -- terminates = ?
