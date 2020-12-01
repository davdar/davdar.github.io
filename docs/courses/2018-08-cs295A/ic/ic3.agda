module ic3 where

---------
-- LIB --
---------

infix 1 begin_
infixr 2 _is-≡_
infix 3 _∎
infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

begin_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
begin x≡y = x≡y

_is-≡_ : ∀ {A : Set} (x : A) {y : A} → x ≡ y → x ≡ y
_ is-≡ x≡y = x≡y

_∎ : ∀ {A : Set} (x : A) → x ≡ x
_ ∎ = refl

--------------
-- IN CLASS --
--------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data ℕ′ : Set where
  -- --------
  -- zero : ℕ

  zero : ℕ′

  -- m : ℕ
  -- ---------
  -- suc m : ℕ

  suc : ℕ′ → ℕ′

e-one : ℕ
e-one = {!!}

_ : e-one ≡ 1
_ = refl

e-zero : ℕ
e-zero = {!!}

e-two : ℕ
e-two = {!!}

e-three : ℕ
e-three = {!!}

_ : e-zero ≡ 0
_ = refl

_ : e-three ≡ 3
_ = refl

e-three′ : ℕ
e-three′ = {!!}

_+_ : ℕ → ℕ → ℕ
m + n = {!!}

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  is-≡    -- is shorthand for
    {!!}
  is-≡    -- inductive case
    {!!}
  is-≡    -- inductive case
    {!!}
  is-≡    -- base case
    {!!}
  is-≡    -- is longhand for
    5
  ∎
  
_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero * n     =  zero
(suc m) * n  =  n + (m * n)

_ =
  begin
    2 * 3
  is-≡    -- inductive case
    {!!}
  is-≡    -- inductive case
    {!!}
  is-≡    -- base case
    {!!}
  is-≡    -- simplify
    6
  ∎
  
_∸_ : ℕ → ℕ → ℕ
m       ∸ zero     =  m
zero    ∸ n        =  zero
(suc m) ∸ (suc n)  =  m ∸ n

_ =
  begin
     3 ∸ 2
  is-≡
     {!!}
  is-≡
     {!!}
  is-≡
     1
  ∎
  
_ =
  begin
     2 ∸ 3
  is-≡
     {!!}
  is-≡
     {!!}
  is-≡
     0
  ∎
  
infixl 6  _+_  _∸_
infixl 7  _*_

_ : 1 + 2 * 3 ∸ 7 ≡ 0
_ = refl

data bin-ℕ : Set where
  bits : bin-ℕ
  _x0 : bin-ℕ → bin-ℕ
  _x1 : bin-ℕ → bin-ℕ
  
inc : bin-ℕ → bin-ℕ
inc n = {!!}

_ : inc (bits x1 x0 x1 x1) ≡ bits x1 x1 x0 x0
_ = refl

to : ℕ → bin-ℕ
to n = {!!}

from : bin-ℕ → ℕ
from n = {!!}

_ : from (bits x1 x0 x1) ≡ 5
_ = refl

_ : to 5 ≡ bits x1 x0 x1
_ = refl
