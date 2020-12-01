module ic4 where

---------
-- LIB --
---------

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

--------------
-- IN CLASS --
--------------

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

+-lunit : ∀ (m : ℕ) → zero + m ≡ m
+-lunit m = {!!}

+-runit : ∀ (m : ℕ) → m + zero ≡ m
+-runit m = {!!}
  
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc m n p = {!!}
  
+-lsuc : ∀ (m n : ℕ) → suc m + n ≡ suc (m + n)
+-lsuc m n = {!!}

+-rsuc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-rsuc m n = {!!}
  
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m n = {!!}

-- now with `rewrite`
  
+-runit′ : ∀ (n : ℕ) → n + zero ≡ n
+-runit′ m = {!!}

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ m n p = {!!}

+-rsuc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-rsuc′ m n = {!!}

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m n = {!!}

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
from (n x0) = 2 * from n
from (n x1) = 2 * from n + 1

from∘inc : ∀ (m : bin-ℕ) → from (inc m) ≡ suc (from m)
from∘inc m = {!!}

from∘to : ∀ (m : ℕ) → from (to m) ≡ m
from∘to m = {!!}

to/from-corr : ∀ (m : bin-ℕ) (n : ℕ) → m ≡ to n → from m ≡ n
to/from-corr m n ε = {!!}
