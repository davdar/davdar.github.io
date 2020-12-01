-- [Nearly all of this material is borrowed from [plfa.Relations]
-- authored by Wen Kokke and Philip Wadler.]
-- 
-- [plfa.Relations]: https://plfa.github.io/Relations/

module la5 where

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

-- The Less-than Relation
-- 
-- On paper, we might define the less-than relation inductively as:
-- 
--     -------------
--     0 ≤ n
-- 
--     m ≤ n
--     -----------------
--     1+m ≤ 1+n
-- 
-- Here is the definition in Agda:

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ}
    --------------
    → zero ≤ n
  suc : ∀ {m n : ℕ}
    → m ≤ n
    -----------------
    → suc m ≤ suc n

-- Here is the “proof term” for 2 ≤ 4

_ : 2 ≤ 5
_ = suc (suc zero)

-- Here agda is inferring the *implicit* arguments m and n. These can
-- be supplied explicitly as well.

_ : 2 ≤ 5
_ = suc {1} {4} (suc {0} {3} (zero {3}))

-- You can also supply implicit arguments by name.

_ : 2 ≤ 5
_ = suc {m = 1} {n = 4} (suc {m = 0} {n = 3} (zero {n = 3}))

_ : 5 ≤ 5
_ = suc (suc (suc (suc (suc zero))))
    
-- Just like + and * had algebraic laws (unit, associativity,
-- commutativity, distributivity), ≤ has relational algebraic laws.

≤-refl : ∀ (n : ℕ) → n ≤ n
≤-refl zero = zero
≤-refl (suc n) = suc (≤-refl n)

-- E: try doing the next proof first by induction on m,n,p.

≤-trans : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
≤-trans n≤p zero = zero
≤-trans (suc n≤p) (suc m≤n) = suc (≤-trans n≤p m≤n)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym zero zero = refl
≤-antisym (suc m≤n) (suc n≤m) rewrite ≤-antisym m≤n n≤m = refl
