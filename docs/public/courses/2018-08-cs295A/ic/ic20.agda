module ic20 where

open import Basics-v7

data exp (N : ℕ) : Set where

instance
  has[+][exp] : ∀ {N} → has[+] (exp N)
  has[+][exp] = record { zero = {!!} ; _+_ = {!!} }

  has[*][exp] : ∀ {N} → has[*] (exp N)
  has[*][exp] = record { one = {!!} ; _*_ = {!!} }

⟦_⟧ : ∀ {N} → exp N → vec[ N ] ℕ → ℕ
⟦ e ⟧ γ = {!!}

-- _ : ∀ x → x + x ≡ ⟦ Var (𝕚 0) + Var (𝕚 0) ⟧ [ x ] 
-- _ = λ x → refl
-- 
-- _ : ∀ x y → (x + y) * x ≡ ⟦ (Var (𝕚 0) + Var (𝕚 1)) * Var (𝕚 0) ⟧ [ x , y ] 
-- _ = λ x y → refl

nf*⟦_⟧ : ∀ {N} → bag (idx N) → vec[ N ] ℕ → ℕ
nf*⟦ xs ⟧ γ = {!!}

nf+⟦_⟧ : ∀ {N} → bag (bag (idx N)) → vec[ N ] ℕ → ℕ
nf+⟦ xss ⟧ γ = {!!}

nf-𝕟 : ∀ {N} → ℕ → bag (bag (idx N))
nf-𝕟 n = {!!}

postulate
  correct[nf-𝕟] : ∀ {N} (n : ℕ) (γ : vec[ N ] ℕ) → nf+⟦ nf-𝕟 {N} n ⟧ γ ≡ n

nf : ∀ {N} → exp N → bag (bag (idx N))
nf e = {!!}

postulate
  correct[nf] : ∀ {N} (e : exp N) (γ : vec[ N ] ℕ) → nf+⟦ nf e ⟧ γ ≡ ⟦ e ⟧ γ


solve_[_≛_] : ∀ {N} (γ : vec[ N ] ℕ) (e₁ e₂ : exp N) {{_ : nf e₁ ≡ nf e₂}} → ⟦ e₁ ⟧ γ ≡ ⟦ e₂ ⟧ γ
solve γ [ e₁ ≛ e₂ ] {{ε}} = {!!}

-- a nontrivial arithmetic equality that is easily discharged by solve
_ : ∀ (x y z : ℕ) → x * (x + x + y + z) ≡ (y * x + z * 1 * x + x * 2 * x + 0) * 1 + 0
_ = λ x y z → {!!}
