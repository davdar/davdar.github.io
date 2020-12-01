module IC3 where

-- UNICODE --

-- ′: \'
-- ↯: \zd
-- ∀: \all
-- ≡: \==
-- 𝔹: \bbB
-- ℕ: \bbN
-- →: \r

-- LIB --

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄ --
-- FROM SCRATCH --
-- ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄ --

data ℕ : Set where
  -- -----
  -- Z : ℕ
  Z : ℕ

  -- n : ℕ
  -- -------
  -- S(n) : ℕ
  S : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

one : ℕ
one = S Z

one′ : ℕ
one′ = 1

_+_ : ℕ → ℕ → ℕ
Z + n = n
S m + n = S (m + n)

lunit[+] : ∀ (m : ℕ) → 0 + m ≡ m
lunit[+] m = ↯

runit[+] : ∀ (m : ℕ) → m + 0 ≡ m
runit[+] Z = ↯
-- runit[+] (S m) rewrite runit[+] m = {!runit[+] m!}
runit[+] (S m) rewrite runit[+] m = {!!}
