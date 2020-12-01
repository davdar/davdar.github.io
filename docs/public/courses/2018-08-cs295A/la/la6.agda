-- [Nearly all of this material is borrowed from [plfa.Relations]
-- authored by Wen Kokke and Philip Wadler.]
-- 
-- [plfa.Relations]: https://plfa.github.io/Relations/

module la6 where

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

-- ≤ is total, which means that for any m and n, either m ≤ n or n ≤
-- m. We first must define total as an inductive proposition:

data Total (m n : ℕ) : Set where
  is-≤ : m ≤ n → Total m n
  is-≥ : n ≤ m → Total m n

-- We could have also defined it instead as:

data Total′ : ℕ → ℕ → Set where
  is-≤′ : ∀ {m n : ℕ} → m ≤ n → Total′ m n
  is-≥′ : ∀ {n m : ℕ} → n ≤ m → Total′ m n

-- The first version uses *parameters* whereas the second uses
-- *indices*. Parameters are preferred when possible. Indices are
-- strictly more general. Indices let you change the index in each
-- rule. E.g., in the definition of ≤, the first argument cannot be
-- defined as a parameter because it is zero in the first case and
-- (suc m) in the second case; likewise for the second parameter
-- because it is a variable n in the first case and (suc n) in the
-- second case.

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = is-≤ zero
≤-total (suc m) zero = is-≥ zero
≤-total (suc m) (suc n) with ≤-total m n
… | is-≤ m≤n = is-≤ (suc m≤n)
… | is-≥ n≥m = is-≥ (suc n≥m)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero n = is-≤ zero
≤-total′ (suc m) zero = is-≥ zero
≤-total′ (suc m) (suc n) = helper (≤-total′ m n)
  where
    helper : Total m n → Total (suc m) (suc n)
    helper (is-≤ x) = is-≤ (suc x)
    helper (is-≥ x) = is-≥ (suc x)

≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m zero = is-≥ zero
≤-total″ zero (suc n) = is-≤ zero
≤-total″ (suc m) (suc n) with ≤-total″ m n
… | is-≤ m≤n = is-≤ (suc m≤n)
… | is-≥ n≥m = is-≥ (suc n≥m)

-- A function f is monotonic if x ≤ y means f(x) ≤ f(y).
-- 
-- E: try doing this by induction on the equality first

+-≤-rmono : ∀ (m n p : ℕ) → n ≤ p → m + n ≤ m + p
+-≤-rmono zero n p n≤p = n≤p
+-≤-rmono (suc m) n p n≤p = suc (+-≤-rmono m n p n≤p)

+-≤-lmono : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-≤-lmono m n zero n≤p rewrite +-runit m | +-runit n = n≤p
+-≤-lmono m n (suc p) n≤p rewrite +-rsuc m p | +-rsuc n p = suc (+-≤-lmono m n p n≤p)

+-≤-lmono′ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-≤-lmono′ m n p m≤n rewrite +-comm m p | +-comm n p = +-≤-rmono p m n m≤n

-- Strict inequality
-- 
--     -------------
--     0 < 1+n
-- 
--     m < n
--     -----------------
--     1+m < 1+n

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ}
    ------------------
    → zero < suc n
  suc : ∀ {m n : ℕ}
    → m < n
    -----------------
    → suc m < suc n

_ : 2 < 5
_ = suc (suc zero)

_ : 4 < 5
_ = suc (suc (suc (suc zero)))

-- Even and odd-ness

mutual 
  data even : ℕ → Set where
    zero : even zero
    suc : ∀ {n}
      → odd n
      → even (suc n)
  data odd : ℕ → Set where
    suc : ∀ {n}
      → even n
      → odd (suc n)

even[4] : even 4
even[4] = suc (suc (suc (suc zero)))

odd[5] : odd 5
odd[5] = suc even[4]

-- Let's prove that even + even = even

mutual
  e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
  e+e≡e zero e[n] = e[n]
  e+e≡e (suc o[m]) e[n] = suc (o+e≡o o[m] e[n])

  o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)
  o+e≡o (suc e[m]) e[n] = suc (e+e≡e e[m] e[n]) 


e+e≡e′ : ∀ {m n : ℕ} → even m → even n → even (m + n)
e+e≡e′ zero e[n] = e[n]
e+e≡e′ (suc (suc e[m])) e[n] = suc (suc (e+e≡e′ e[m] e[n]))
