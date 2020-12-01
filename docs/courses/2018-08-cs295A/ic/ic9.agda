module ic9 where

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
  zero : ∀ {n : ℕ} → zero ≤ n
  suc : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ} → zero < suc n
  suc : ∀ {m n : ℕ} → m < n → suc m < suc n

infixr 2 _×_
data _×_ : Set → Set → Set where
  ⟨_,_⟩ : ∀ {A B : Set}
    → A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

infix 1 _⊎_
data _⊎_ : Set → Set → Set where
  inj₁ : ∀ {A B : Set} → A → A ⊎ B
  inj₂ : ∀ {A B : Set} → B → A ⊎ B

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

infix 20 ¬_
¬_ : Set → Set
¬ A = A → ⊥

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
  -- < --
  <-irrefl : ∀ (m : ℕ) → ¬ (m ≤ m)
  <-trans : ∀ {m n p : ℕ} → n < p → m < n → m < p
  <-asym : ∀ {m n : ℕ} → ¬ (m < n × n < m)

--------------
-- IN CLASS --
--------------

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤?_
_≤?_ : ℕ → ℕ → Bool
m ≤? n = {!!}

_ : 2 ≤ 4
_ = {!!}

_ : (2 ≤? 4) ≡ true
_ = {!!}

_ : 10 ≤ 10
_ = {!!}

_ : (10 ≤? 10) ≡ true
_ = {!!}

cor[≤?]-L : ∀ {m n : ℕ} → m ≤ n → (m ≤? n) ≡ true
cor[≤?]-L ε = {!!}

cor[≤?]-R : ∀ (m n : ℕ) → (m ≤? n) ≡ true → m ≤ n
cor[≤?]-R m n = {!!}

data Ordering (m n : ℕ) : Set where
  LT : m < n → Ordering m n
  EQ : m ≡ n → Ordering m n
  GT : n < m → Ordering m n

_∇_ : ∀ (m n : ℕ) → Ordering m n
m ∇ n = {!!}

_ : 2 ∇ 4 ≡ LT (suc (suc zero))
_ = {!!}
  
data Comparison : Set where
  LT : Comparison
  EQ : Comparison
  GT : Comparison

_∇?_ : ℕ → ℕ → Comparison
m ∇? n = {!!}

_ : 2 ∇? 4 ≡ LT
_ = {!!}

data Link {m n : ℕ} : Comparison → Ordering m n → Set where
  LT : ∀ {ε : m < n} → Link LT (LT ε)
  EQ : ∀ {ε : m ≡ n} → Link EQ (EQ ε)
  GT : ∀ {ε : n < m} → Link GT (GT ε)

cor[∇?]-L : ∀ (m n : ℕ) → Link (m ∇? n) (m ∇ n)
cor[∇?]-L zero zero = {!!}
cor[∇?]-L zero (suc n) = {!!}
cor[∇?]-L (suc m) zero = {!!}
cor[∇?]-L (suc m) (suc n) = {!!}
