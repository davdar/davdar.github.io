module ic17 where

open import Basics-v4

data tree : ℕ → Set where
  L : tree 0
  2[_<_>_] : ∀ {n}
    → tree n
    → ℕ
    → tree n
    → tree (Suc n)
  3[_<_>_<_>_] : ∀ {n}
    → tree n
    → ℕ
    → tree n
    → ℕ
    → tree n
    → tree (Suc n)

t1 : tree 2
t1 = 3[ 2[ L < 1 > L ] < 2 > 3[ L < 3 > L < 4 > L ] < 5 > 2[ L < 6 > L ] ]

data context (m : ℕ) : ℕ → Set where
  T : context m m
  2[X<_>_/_] : ∀ {n}
    → ℕ
    → tree n
    → context m (Suc n)
    → context m n
  2[_<_>X/_] : ∀ {n}
    → tree n
    → ℕ
    → context m (Suc n)
    → context m n
  3[X<_>_<_>_/_] : ∀ {n}
    → ℕ
    → tree n
    → ℕ
    → tree n
    → context m (Suc n)
    → context m n
  3[_<_>X<_>_/_] : ∀ {n}
    → tree n
    → ℕ → ℕ
    → tree n
    → context m (Suc n)
    → context m n
  3[_<_>_<_>X/_] : ∀ {n}
    → tree n
    → ℕ
    → tree n
    → ℕ
    → context m (Suc n)
    → context m n

zip : ∀ {m n} → tree n → context m n → tree m
zip t κ = {!!}

first-context : ∀ {m n} → tree n → context m n → context m Zero
first-context t κ = {!!}
