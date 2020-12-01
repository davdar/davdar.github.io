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

module hw1 where

---------
-- LIB --
---------

module Lib where
  infix 1 begin_
  infixr 2 _is-≡_ _is-≡[_]_
  infix 3 _∎
  infix 4 _≡_
  infixl 6 _+_ _∸_
  infixl 7 _*_

  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x
  
  {-# BUILTIN EQUALITY _≡_ #-}
  
  begin_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y
  
  _is-≡_ : ∀ {A : Set} (x : A) {y : A} → x ≡ y → x ≡ y
  _ is-≡ x≡y = x≡y
  
  _is-≡[_]_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ is-≡[ refl ] y≡z = y≡z
  
  _∎ : ∀ {A : Set} (x : A) → x ≡ x
  _ ∎ = refl
  
  cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl
  
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
  
  +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
  +-assoc zero n p =
    begin
      (zero + n) + p
    is-≡
      n + p
    is-≡
     zero + (n + p)
    ∎
  +-assoc (suc m) n p =
    begin
      (suc m + n) + p
    is-≡
      suc (m + n) + p
    is-≡
      suc ((m + n) + p)
    is-≡[ cong suc (+-assoc m n p) ]
      suc (m + (n + p))
    is-≡
      suc m + (n + p)
    ∎
  
  +-runit : ∀ (m : ℕ) → m + zero ≡ m
  +-runit zero =
    begin
      zero + zero
    is-≡
      zero
    ∎
  +-runit (suc m) =
    begin
      suc m + zero
    is-≡
      suc (m + zero)
    is-≡[ cong suc (+-runit m) ]
      suc m
    ∎
  
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-suc zero n =
    begin
      zero + suc n
    is-≡
      suc n
    is-≡
      suc (zero + n)
    ∎
  +-suc (suc m) n =
    begin
      suc m + suc n
    is-≡
      suc (m + suc n)
    is-≡[ cong suc (+-suc m n) ]
      suc (suc (m + n))
    is-≡
      suc (suc m + n)
    ∎
  
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm m zero =
    begin
      m + zero
    is-≡[ +-runit m ]
      m
    is-≡
      zero + m
    ∎
  +-comm m (suc n) =
    begin
      m + suc n
    is-≡[ +-suc m n ]
      suc (m + n)
    is-≡[ cong suc (+-comm m n) ]
      suc (n + m)
    is-≡
      suc n + m
    ∎
open Lib public

----------------
-- ASSIGNMENT --
----------------

-- # E1: [★]
-- Write out 7 in longhand
seven : ℕ
seven = {!!}

-- this will fail if you got E1 wrong!
seven-is-correct : seven ≡ 7
seven-is-correct = refl

-- # E2: [★]
-- Compute 3 + 4, writing out your reasoning as a chain of equations.
three+four : 3 + 4 ≡ 7
three+four =
  begin
    3 + 4
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    7
  ∎

-- # E3: [★]
-- Compute 3 * 4, writing out your reasoning as a chain of equations.
three*four : 3 * 4 ≡ 12
three*four = begin
    3 * 4
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    12
  ∎

-- # E4: [★★]
-- Define exponentiation, which is given by the following equations:
--     m ^ 0        =  1
--     m ^ (1 + n)  =  m * (m ^ n)
_^_ : ℕ → ℕ → ℕ
m ^ n = {!!}

-- this will fail if you got E4 wrong!
^-is-correct : 2 ^ 5 ≡ 32
^-is-correct = refl

-- E5: [★]
-- Compute 3 ^ 4, writing out your reasoning as a chain of equations.
three^four : 3 ^ 4 ≡ 81
three^four =
  begin
    3 ^ 4
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    81
  ∎

-- E6: [★]
-- Compute 5 ∸ 3, writing out your reasoning as a chain of equations.
five∸three : 5 ∸ 3 ≡ 2
five∸three =
  begin
    5 ∸ 3
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    2
  ∎

-- E7: [★]
-- Compute 3 ∸ 5, writing out your reasoning as a chain of equations.
three∸five : 3 ∸ 5 ≡ 0
three∸five =
  begin
    3 ∸ 5
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    {!!}
  is-≡
    0
  ∎

-- E8: [★★]
-- Show m + (n + p) ≡ n + (m + p) for all naturals m, n, and p. No
-- induction is needed, just apply the previous results which show
-- addition is associative and commutative.
-- (Hint: use rewrite.)
+-swap : ∀ (m n p : ℕ) → (m + n) + p ≡ n + (m + p)
+-swap m n p = {!!}

-- E9: [★★★]
-- Show multiplication distributes over addition, that is,
-- (m + n) * p ≡ m * p + n * p for all naturals m, n, and p.
-- (Hint: proceed by induction on m.)
-- (Hint: use rewrite.)
-- (Hint: use lemma +-assoc and helper sym.)
*-+-rdistrib : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-+-rdistrib m n p = {!!}

-- E10: [★★★]
-- Show multiplication is associative, that is,
-- (m * n) * p ≡ m * (n * p)
-- (Hint: proceed by induction on m.)
-- (Hint: use rewrite.)
-- (Hint: use lemma *-distrib-+.)
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc m n p = {!!}

-- E11: [★★★]
-- Show multiplication is commutative, that is, m * n ≡ n * m for all
-- naturals m and n. As with commutativity of addition, you will need
-- to formulate and prove suitable lemmas.
module *-comm-lemmas where
  -- (Hint: proceed by induction on m.)
  *-rzero : ∀ (m : ℕ) → m * zero ≡ zero
  *-rzero m = {!!}

  -- (Hint: proceed by induction on m.)
  -- (Hint: use rewrite.)
  *-runit : ∀ (m : ℕ) → m * 1 ≡ m
  *-runit m = {!!}

  -- (Hint: proceed by induction on m.)
  -- (Hint: use rewrite.)
  -- (Hint: use lemmas.)
  *-+-ldistrib : ∀ (m n p : ℕ) → m * (n + p) ≡ m * n + m * p
  *-+-ldistrib m n p = {!!}
open *-comm-lemmas public

-- (Hint: proceed by induction on m.)
-- (Hint: use rewrite.)
-- (Hint: use lemmas.)
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m n = {!!}

-- E12: [★★]
-- Show zero ∸ m ≡ zero for all naturals m. Did your proof require
-- induction?
0∸n≡0 : ∀ (m : ℕ) → zero ∸ m ≡ zero
0∸n≡0 m = {!!}

-- E13: [★★★]
-- Show that monus associates with addition, that is,
-- m ∸ n ∸ p ≡ m ∸ (n + p) for all naturals m, n, and p.
-- (Hint: proceed by induction on m and n.)
∸-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-assoc m n p = {!!}
