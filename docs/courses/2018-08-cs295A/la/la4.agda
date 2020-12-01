-- [Nearly all of this material is borrowed from [plfa.Induction]
-- authored by Wen Kokke and Philip Wadler.]
-- 
-- [plfa.Induction]: https://plfa.github.io/Induction/
-- 
-- # Induction

module la4 where

-------------
-- LIBRARY --
-------------

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
begin x≡y = x≡y

_is-≡_ : ∀ {A : Set} (x : A) {y : A} → x ≡ y → x ≡ y
_ is-≡ x≡y = x≡y

_is-≡[_]_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ is-≡[ refl ] y≡z = y≡z

_∎ : ∀ {A : Set} (x : A) → x ≡ x
_ ∎ = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

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
zero * n     =  zero
(suc m) * n  =  n + (m * n)

_∸_ : ℕ → ℕ → ℕ
m       ∸ zero     =  m
zero    ∸ (suc n)  =  zero
(suc m) ∸ (suc n)  =  m ∸ n

-- # Properties of operators
-- 
-- Operators pop up all the time, and mathematicians have agreed on names
-- for some of the most common properties.
-- 
-- - *Unit (aka Identity):* `+` has left unit `0` if `0 + n ≡ n`, and
--   right unit `0` if `n + 0 ≡ n`, for all `n`. A value that is both a
--   left and right unit is just called a unit.
-- 
-- - *Associative:* `+` is associative if the location of parentheses
--   does not matter: `(m + n) + p ≡ m + (n + p)`, for all `m`, `n`, and
--   `p`.
-- 
-- - *Commutative:* `+` is commutative if order or arguments does not
--   matter: `m + n ≡ n + m`, for all `m` and `n`.
-- 
-- - *Distributive:* `*` distributes over operator `+` from the
--   left if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`, and `p`,
--   and from the right if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`,
--   `p`, and `q`. An operator that distribues from both the left and the
--   right is just called distributive.

_ : 4 + 0 ≡ 4
_ = refl

_ : 0 + 4 ≡ 4
_ = refl

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = refl

_ : 2 + 5 ≡ 5 + 2
_ = refl

_ : 2 * (3 + 4) ≡ 2 * 3 + 2 * 4
_ = refl

_ : (2 + 3) * 4 ≡ 2 * 4 + 3 * 4
_ = refl

-- Addition has unit `0` and multiplication has unit `1`; addition and
-- multiplication are both associative and commutative; and
-- multiplications distributes over addition.
-- 
-- ## Units

+-lunit : ∀ (m : ℕ) → zero + m ≡ m
+-lunit m =
  begin
    zero + m
  is-≡
    m
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

-- ## Associativity

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

-- ## Commutativity
-- 
-- We also need a lemma about addition after incrementing:

+-lsuc : ∀ (m n : ℕ) → suc m + n ≡ suc (m + n)
+-lsuc m n = refl

+-rsuc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-rsuc zero n =
  begin
    zero + suc n
  is-≡
    suc n
  is-≡
    suc (zero + n)
  ∎
+-rsuc (suc m) n =
  begin
    suc m + suc n
  is-≡
    suc (m + suc n)
  is-≡[ cong suc (+-rsuc m n) ]
    suc (suc (m + n))
  is-≡
    suc (suc m + n)
  ∎

-- Finally, here is commutativity:

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
  is-≡[ +-rsuc m n ]
    suc (m + n)
  is-≡[ cong suc (+-comm m n) ]
    suc (n + m)
  is-≡
    suc n + m
  ∎

-- ## Using rewrite

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-runit′ : ∀ (n : ℕ) → n + zero ≡ n
+-runit′ zero = refl
+-runit′ (suc n) rewrite +-runit′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-runit′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- ## Binary Nats

data bin-ℕ : Set where
  bits : bin-ℕ
  _x0 : bin-ℕ → bin-ℕ
  _x1 : bin-ℕ → bin-ℕ

inc : bin-ℕ → bin-ℕ
inc bits = bits x1
inc (n x0) = n x1
inc (n x1) = (inc n) x0

infixl 6  _bin-+_
_bin-+_ : bin-ℕ → bin-ℕ → bin-ℕ
bits bin-+ n = n
m bin-+ bits = m
(m x0) bin-+ (n x0) = (m bin-+ n) x0
(m x0) bin-+ (n x1) = (m bin-+ n) x1
(m x1) bin-+ (n x0) = (m bin-+ n) x1
(m x1) bin-+ (n x1) = inc ((m bin-+ n) x1)

to : ℕ → bin-ℕ
to zero = bits
to (suc n) = inc (to n)

from : bin-ℕ → ℕ
from bits = 0
from (n x0) = from n + from n
from (n x1) = 1 + from n + from n

-- Let's prove:
-- 
--     from (inc x) ≡ suc (from x)
--     to (from n) ≡ n
--     from (to x) ≡ x

from∘inc : ∀ (m : bin-ℕ) → from (inc m) ≡ suc (from m)
from∘inc bits = refl
from∘inc (m x0) = refl
from∘inc (m x1) rewrite from∘inc m | +-rsuc (from m) (from m) = refl

from∘to : ∀ (m : ℕ) → from (to m) ≡ m
from∘to zero = refl
from∘to (suc m) rewrite from∘inc (to m) | from∘to m = refl

to/from-corr : ∀ (m : bin-ℕ) (n : ℕ) → m ≡ to n → from m ≡ n
to/from-corr m n ε rewrite ε = from∘to n

-- The following is not provable:
-- 
--   to (from m) ≡ m
-- 
-- because `ℕ` is a *canonical* representation, whereas `bin-ℕ` is not.
-- E.g., there are multiple ways to represent `0` in `bin-ℕ`:
-- 
--     zero-1 = nil
--     zero-2 = x0 nil
--     zero-3 = x0 x0 nil
-- 
-- whereas the `from` mapping from `ℕ` to `bin-ℕ` maps `0` just to `nil`.
-- This means the following are not true, which are counterexamples to
-- the full isomorphism.
-- 
--     to (from (x0 nil)) ≡ nil ≢ x0 nil
