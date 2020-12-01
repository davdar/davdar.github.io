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

module hw4 where

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

infixr 2 _×_
data _×_ : Set → Set → Set where
  ⟨_,_⟩ : ∀ {A B : Set}
    → A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

infix 1 _⊎_
data _⊎_ : Set → Set → Set where
  inj₁ : ∀ {A B : Set}
    → A
      -----
    → A ⊎ B

  inj₂ : ∀ {A B : Set}
    → B
      -----
    → A ⊎ B

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

_≢_ : ∀ {A : Set} (x y : A) → Set
x ≢ y = ¬ x ≡ y

infix 2 ∃
syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B
data ∃ (A : Set) (B : A → Set) : Set where
  ⟨∃_,_⟩ : (x : A) → B x → ∃ A B

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

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

----------------
-- ASSIGNMENT --
----------------

-- here is the definition of binary numbers

data bin-ℕ : Set where
  bits : bin-ℕ
  _x0 : bin-ℕ → bin-ℕ
  _x1 : bin-ℕ → bin-ℕ

-- remember, the parenthesis for bit strings go like this:
-- 
--     bits x1              -- this is   1 in bits, aka 1
--     (bits x1) x0         -- this is  10 in bits, aka 2
--     (bits x1) x1         -- this is  11 in bits, aka 3
--     ((bits x1) x0) x0    -- this is 100 in bits, aka 4
--     ((bits x1) x0) x1    -- ... 5
--     ((bits x1) x1) x0    -- ... 6
--     ((bits x1) x1) x1    -- ... 7
--
-- these are all equivalent to the following, which have an extra zero
-- in front, which doesn't change the meaning of the numbers:
-- remember, the parenthesis for bit strings go like this:
-- 
--     (bits x0) x1              -- this is   01 in bits, aka 1
--     ((bits x0) x1) x0         -- this is  010 in bits, aka 2
--     ((bits x0) x1) x1         -- this is  011 in bits, aka 3
--     (((bits x0) x1) x0) x0    -- this is 0100 in bits, aka 4
--     (((bits x0) x1) x0) x1    -- ... 5
--     (((bits x0) x1) x1) x0    -- ... 6
--     (((bits x0) x1) x1) x1    -- ... 7

-- the increment function on bits
inc : bin-ℕ → bin-ℕ
inc bits = bits x1
inc (n x0) = n x1
inc (n x1) = (inc n) x0

-- the plus function on bits
infixl 6  _bin-+_
_bin-+_ : bin-ℕ → bin-ℕ → bin-ℕ
bits bin-+ n = n
m bin-+ bits = m
(m x0) bin-+ (n x0) = (m bin-+ n) x0
(m x0) bin-+ (n x1) = (m bin-+ n) x1
(m x1) bin-+ (n x0) = (m bin-+ n) x1
(m x1) bin-+ (n x1) = inc ((m bin-+ n) x1)

-- the mapping from natural numbers to bits
to : ℕ → bin-ℕ
to zero = bits
to (suc n) = inc (to n)

-- the mapping back from bits to natural numbers
from : bin-ℕ → ℕ
from bits = 0
from (n x0) = from n + from n
from (n x1) = 1 + from n + from n

-- here is a predicate for bit strings which start with a 1; here are
-- examples of bit strings that start with a 1
-- ‣ bits x1
-- ‣ bits x1 x0
-- ‣ bits x1 x1
-- ‣ bits x1 x0 x0
-- ‣ bits x1 x0 x1
-- ‣ bits x1 x1 x0
-- ‣ bits x1 x1 x1
-- ‣ etc.

data Leading-1 : bin-ℕ → Set where
  [one] : Leading-1 (bits x1)
  [x0] : ∀ (n : bin-ℕ) → Leading-1 n → Leading-1 (n x0)
  [x1] : ∀ (n : bin-ℕ) → Leading-1 n → Leading-1 (n x1)

-- here is 1
one : bin-ℕ
one = bits x1

-- here is 2
two : bin-ℕ
two = bits x1 x0

-- here is 3
three : bin-ℕ
three = bits x1 x1

-- E1: [★]
-- prove that one and two have leading a leading one

leadine-1-one : Leading-1 one
leadine-1-one = {!!}

leading-1-two : Leading-1 two
leading-1-two = {!!}

leading-1-three : Leading-1 three
leading-1-three = {!!}

-- E2: [★]
-- prove that one with a zero in front does not have a leading one
-- HINT: do deep case analysis

not-leading-1-one : ¬ Leading-1 (bits x0 x1)
not-leading-1-one l = {!!}

-- E3: [★★]
-- prove that the mapping from ℕ to bin-ℕ always gives numbers with
-- leading ones, or the canonical value for zero
-- HINT: do induction on the evidence for (Leading-1 n)

leading-one-inc : ∀ (n : bin-ℕ) → Leading-1 n → Leading-1 (inc n)
leading-one-inc n l = {!!}

-- E4: [★★]
-- prove the lsuc lemma for bin-+, which is the plus function for bit
-- strings
-- HINT: do induction on m and n

bin-+-lsuc : ∀ (m n : bin-ℕ) → (inc m) bin-+ n ≡ inc (m bin-+ n)
bin-+-lsuc m n = {!!}

-- E5: [★★]
-- prove that if a number has a leading 1, then adding it to itself
-- (i.e., multiplying by 2) is the same as adding the bit 0 to the
-- right, i.e., shifting all bits left by one
-- HINT: do induction on the evidence or (Leading-1 m)

bin-+-*2 : ∀ (m : bin-ℕ) → Leading-1 m → m bin-+ m ≡ m x0
bin-+-*2 m l = {!!}

-- E6: [★★]
-- prove that the `to` mapping after addition is the same as the bin-+
-- function after `to` mapping
-- HINT: do induction on m and appeal to bin-+-lsuc
  
to∘+ : ∀ (m n : ℕ) → to (m + n) ≡ to m bin-+ to n
to∘+ m n = {!!}

-- E7: [★]
-- prove that if n is literally `bits`, i.e., the canonical
-- representation for zero, then mapping to natural numbers and back
-- gives the same bit string.
-- HINT: use rewrite

to∘from-zero : ∀ (n : bin-ℕ) → n ≡ bits → to (from n) ≡ n
to∘from-zero .bits refl = {!!}

-- E8: [★★★]
-- prove that if n has a leading 1, then mapping to natural numbers
-- and back gives the same bit string.
-- HINT: do induction on the evidence for (Leading-1 n), and appeal to
-- lemmas to∘+ and bin-+-*2

to∘from-leading-1 : ∀ (n : bin-ℕ) → Leading-1 n → to (from n) ≡ n
to∘from-leading-1 .(bits x1) [one] = refl
to∘from-leading-1 .(n x0) ([x0] n l) rewrite to∘+ (from n) (from n) | to∘from-leading-1 n l | bin-+-*2 n l = refl
to∘from-leading-1 .(n x1) ([x1] n l) = {!!}

-- E9: [★]
-- prove that if n is either `bits` or has a leading-1, then mapping
-- to natural numbers and back gives the same bit string
-- HINT: don't do induction, just use lemmas to∘from-zero and
-- to∘from-leading-1

to∘from : ∀ (n : bin-ℕ) → n ≡ bits ⊎ Leading-1 n → to (from n) ≡ n
to∘from n el = {!!}
