module IC4 where

-- UNICODE --

{-
    ×    \x
    ′    \'
    →    \r
    ↯    \zd
    ∀    \all
    ∸    \-.
    ≡    \==
    𝔹    \bbB
    ◇    \di
    ⊚    \oo
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

-- ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄ --
-- FROM SCRATCH --
-- ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄ --
