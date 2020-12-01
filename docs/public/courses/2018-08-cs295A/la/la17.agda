module la17 where

open import Basics-v4

data tree : ℕ → Set where
  L : tree 0
  2[_<_>_] : ∀ {n} → tree n → ℕ → tree n → tree (Suc n)
  3[_<_>_<_>_] : ∀ {n} → tree n → ℕ → tree n → ℕ → tree n → tree (Suc n)

t1 : tree 2
t1 = 3[ 2[ L < 1 > L ] < 2 > 3[ L < 3 > L < 4 > L ] < 5 > 2[ L < 6 > L ] ]

data context (m : ℕ) : ℕ → Set where
  T : context m m
  2[X<_>_/_] : ∀ {n} → ℕ → tree n → context m (Suc n) → context m n
  2[_<_>X/_] : ∀ {n} → tree n → ℕ → context m (Suc n) → context m n
  3[X<_>_<_>_/_] : ∀ {n} → ℕ → tree n → ℕ → tree n → context m (Suc n) → context m n
  3[_<_>X<_>_/_] : ∀ {n} → tree n → ℕ → ℕ → tree n → context m (Suc n) → context m n
  3[_<_>_<_>X/_] : ∀ {n} → tree n → ℕ → tree n → ℕ → context m (Suc n) → context m n

zip : ∀ {m n} → tree n → context m n → tree m
zip t T = t
zip t₁ 2[X< x > t₂ / κ ] = zip 2[ t₁ < x > t₂ ] κ
zip t₂ 2[ t₁ < x >X/ κ ] = zip 2[ t₁ < x > t₂ ] κ
zip t₁ 3[X< x₁ > t₂ < x₂ > t₃ / κ ] = zip 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ
zip t₂ 3[ t₁ < x₁ >X< x₂ > t₃ / κ ] = zip 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ
zip t₃ 3[ t₁ < x₁ > t₂ < x₂ >X/ κ ] = zip 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ

first-context : ∀ {m n} → tree n → context m n → context m Zero
first-context L κ = κ
first-context 2[ t₁ < x > t₂ ] κ = first-context t₁ 2[X< x > t₂ / κ ]
first-context 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ = first-context t₁ 3[X< x₁ > t₂ < x₂ > t₃ / κ ]
