module ic6 where

---------
-- LIB --
---------

infix 4 _≡_
infixl 6 _+_ _∸_
infixl 7 _*_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n     =  zero
(suc m) * n  =  n + (m * n)

_∸_ : ℕ → ℕ → ℕ
m       ∸ zero     =  m
zero    ∸ (suc n)  =  zero
(suc m) ∸ (suc n)  =  m ∸ n

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ}
    --------------
    → zero ≤ n
  suc : ∀ {m n : ℕ}
    → m ≤ n
    -----------------
    → suc m ≤ suc n

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
  -- ≤ --
  ≤-refl : ∀ (m : ℕ) → m ≤ m
  ≤-trans : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
  ≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n

--------------
-- IN CLASS --
--------------

data Total (m n : ℕ) : Set where
  -- m ≤ n
  -- ----------
  -- Total m n
  --
  -- n ≤ m
  -- -----------
  -- Total m n

data Total′ : ℕ → ℕ → Set where
  -- m ≤ n
  -- ----------
  -- Total m n
  --
  -- n ≤ m
  -- -----------
  -- Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total m n = {!!}

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ m n = {!!}

≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m n = {!!}

+-≤-rmono : ∀ (m n p : ℕ) → n ≤ p → m + n ≤ m + p
+-≤-rmono m n p n≤p = {!!}

+-≤-lmono : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-≤-lmono m n p n≤p = {!!}

+-≤-lmono′ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-≤-lmono′ m n p m≤n = {!!}

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  -- ------------------
  -- zero < suc n
  --
  -- m < n
  -- -----------
  -- suc m < suc n

_ : 2 < 5
_ = {!!}

_ : 4 < 5
_ = {!!}

mutual 
  data even : ℕ → Set where
    -- ----------
    -- even zero
    --
    -- odd n
    -- -----------
    -- even (suc n)
  data odd : ℕ → Set where
    -- even n
    -- ------------
    -- odd (suc n)

even[4] : even 4
even[4] = {!!}

odd[5] : odd 5
odd[5] = {!!}

mutual
  e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
  e+e≡e e[m] e[n] = {!!}

  o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)
  o+e≡o e[m] e[n] = {!!}

e+e≡e′ : ∀ {m n : ℕ} → even m → even n → even (m + n)
e+e≡e′ e[m] e[n] = {!!}
