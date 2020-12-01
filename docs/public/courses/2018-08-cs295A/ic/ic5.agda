module ic5 where

-------------
-- LIBRARY --
-------------

infix 4 _≡_
infixl 6 _+_ _∸_
infixl 7 _*_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n     =  zero
(suc m) * n  =  n + (m * n)

_∸_ : ℕ → ℕ → ℕ
m       ∸ zero     =  m
zero    ∸ (suc n)  =  zero
(suc m) ∸ (suc n)  =  m ∸ n

postulate
  -- + --
  +-runit : ∀ (m : ℕ) → m + zero ≡ m
  +-rsuc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-assoc : ∀ (m n p : ℕ) → m + n + p ≡ m + (n + p)
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  -- * --
  *-rzero : ∀ (m : ℕ) → m * zero ≡ zero
  *-runit : ∀ (m : ℕ) → m * 1 ≡ m
  *-rsuc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
  *-assoc : ∀ (m n p : ℕ) → m * n * p ≡ m * (n * p)
  *-comm : ∀ (m n : ℕ) → m * n ≡ n * m

--------------
-- IN CLASS --
--------------

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  -- --------------
  -- zero ≤ n
  --
  -- m ≤ n
  -- -----------------
  -- suc m ≤ suc n

_ : 2 ≤ 5
_ = {!!}

_ : 2 ≤ 5
_ = {!!}

_ : 2 ≤ 5
_ = {!!}

_ : 5 ≤ 5
_ = {!!}
    
≤-refl : ∀ (n : ℕ) → n ≤ n
≤-refl n = {!!}

≤-trans : ∀ (m n p : ℕ) → n ≤ p → m ≤ n → m ≤ p
≤-trans m n p n≤p m≤n = {!!}

≤-antisym : ∀ (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
≤-antisym m n m≤n n≤m = {!!}
