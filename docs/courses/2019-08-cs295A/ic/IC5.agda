module IC5 where

-- UNICODE --

{-
    ×    \x
    ε    \epsilon
    ′    \'
    ℕ    \bbN
    →    \r
    ↯    \zd
    ⇄    \rl
    ∀    \all
    ∸    \-.
    ≡    \==
    ≤    \<=
    ⊚    \oo
    ⊴    \t<=
    ⋈    \bow
    ⋚    \<=>=
    ◇    \di
    ⩎    \hm
    𝔹    \bbB
-}

-- LIB --

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x

◇ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
◇ ↯ = ↯

infixl 8 _⊚_
_⊚_ : ∀ {A : Set} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
↯ ⊚ ↯ = ↯

{-# BUILTIN EQUALITY _≡_ #-}

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

infixl 5 _+_
_+_ : ℕ → ℕ → ℕ
Z    + n  =  n
(S m) + n  =  S (m + n)

postulate
  commu[+] : ∀ (m n : ℕ) → m + n ≡ n + m

{-# BUILTIN NATURAL ℕ #-}

-- ⌄⌄⌄⌄⌄⌄⌄⌄ --
-- IN CLASS --
-- ⌄⌄⌄⌄⌄⌄⌄⌄ --

-- “count up from zero to LHS”
infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  Z : ∀ {n} → Z ≤ n
  S : ∀ {m n} → m ≤ n → S m ≤ S n

xRx[≤] : ∀ (m : ℕ) → m ≤ m
xRx[≤] m = {!!}

_⊚[≤]_ : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
n≤p ⊚[≤] m≤n = {!!}

_⋈[≤]_ : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
m≤n ⋈[≤] n≤m = {!!}

rmono[+/≤] : ∀ (m n p : ℕ) → n ≤ p → m + n ≤ m + p
rmono[+/≤] m n p n≤p = {!!}

lmono[+/≤] : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
lmono[+/≤] m n p m≤n = {!!}

-- “count down from RHS to LHS”
infix 4 _⊴_
data _⊴_ : ℕ → ℕ → Set where
  Z : ∀ {n} → n ⊴ n
  S : ∀ {m n} → m ⊴ n → m ⊴ S n

xRx[⊴]  : ∀ (m : ℕ) → m ⊴ m
xRx[⊴] m = {!!}

_⊚[⊴]_ : ∀ {m n p : ℕ} → n ⊴ p → m ⊴ n → m ⊴ p
n⊴p ⊚[⊴] m⊴n = {!!}
