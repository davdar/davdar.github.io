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

module hw2 where

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

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ}
    ------------------
    → zero < suc n
  suc : ∀ {m n : ℕ}
    → m < n
    -----------------
    → suc m < suc n
  
data Total (m n : ℕ) : Set where
  is-≤ :
    m ≤ n
    -----------
    → Total m n
  is-≥ :
    n ≤ m
    -----------
    → Total m n

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
  ≤-total : ∀ (m n : ℕ) → Total m n
  -- +-≤ --
  +-≤-lmono : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
  +-≤-rmono : ∀ (m n p : ℕ) → n ≤ p → m + n ≤ m + p
  -- Even and odd --
  e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
  o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

----------------
-- ASSIGNMENT --
----------------

-- # E1: [★★]
-- Prove that * is monotonic on the right
-- Hint: do induction on m
-- Hint: use ≤-trans, +-≤-lmono and  +-≤-rmono

*-≤-rmono : ∀ (m n p : ℕ) → n ≤ p → m * n ≤ m * p
*-≤-rmono m n p = {!!}

-- # E2: [★]
-- Prove that < is transitive
-- Hint: do induction on m≤n

<-trans : ∀ {m n p : ℕ} → n < p → m < n → m < p
<-trans n<p m<n = {!!}

-- # E3: [★★★]
-- Prove that either m < n, m ≡ n, or m > n for all m and n
-- Hint: do induction on both m and n
-- Hint: use a `with` pattern for the inductive hypothesis

data Trichotomy (m n : ℕ) : Set where
  is-< : m < n → Trichotomy m n
  is-≡ : m ≡ n → Trichotomy m n
  is-> : n < m → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy m n = {!!}

-- #E4: [★★★]
-- Prove that:
-- (suc m ≤ n) and (m < n) are isomorphic propositions, and
-- (m ≤ n) and (m < suc n)

-- Hint: do induction on m≤n
≤-<-iso-to : ∀ {m n : ℕ} → m ≤ n → m < suc n
≤-<-iso-to m≤n = {!!}

-- Hint: use ≤-<-iso-to
≤-<-iso-to′ : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-<-iso-to′ s[m]≤n = {!!}

-- Hint: do induction on m<n
≤-<-iso-fr : ∀ {m n : ℕ} → m < n → suc m ≤ n
≤-<-iso-fr m<n = {!!}

-- Hint: use ≤-<-iso-fr
≤-<-iso-fr′ : ∀ {m n : ℕ} → m < suc n → m ≤ n
≤-<-iso-fr′ m<s[n] = {!!}

-- #E5: [★★]
-- Prove that odd plus odd is even

mutual
  -- Hint: do induction on o[m]
  -- Hint: use e+o≡o
  o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
  o+o≡e o[m] o[n] = {!!}

  -- Hint: do induction on e[m]
  -- Hint: use o+o≡e
  e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)
  e+o≡o e[m] o[n] = {!!}
