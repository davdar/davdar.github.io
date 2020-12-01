module la20 where

open import Basics-v7

data exp (N : ℕ) : Set where
  Lit : ℕ → exp N
  Var : idx N → exp N
  _`+_ : exp N → exp N → exp N
  _`*_ : exp N → exp N → exp N

instance
  has[+][exp] : ∀ {N} → has[+] (exp N)
  has[+][exp] = record { zero = Lit 0 ; _+_ = _`+_ }

  has[*][exp] : ∀ {N} → has[*] (exp N)
  has[*][exp] = record { one = Lit 1 ; _*_ = _`*_ }

⟦_⟧ : ∀ {N} → exp N → vec[ N ] ℕ → ℕ
⟦ Lit n ⟧ γ = n
⟦ Var x ⟧ γ = γ [[ x ]]
⟦ e₁ `+ e₂ ⟧ γ = ⟦ e₁ ⟧ γ + ⟦ e₂ ⟧ γ
⟦ e₁ `* e₂ ⟧ γ = ⟦ e₁ ⟧ γ * ⟦ e₂ ⟧ γ

_ : ∀ x → x + x ≡ ⟦ Var (𝕚 0) + Var (𝕚 0) ⟧ [ x ] 
_ = λ x → refl

_ : ∀ x y → (x + y) * x ≡ ⟦ (Var (𝕚 0) + Var (𝕚 1)) * Var (𝕚 0) ⟧ [ x , y ] 
_ = λ x y → refl

nf*⟦_⟧ : ∀ {N} → bag (idx N) → vec[ N ] ℕ → ℕ
nf*⟦ xs ⟧ γ = reduce [*] xs λ x → γ [[ x ]]

nf+⟦_⟧ : ∀ {N} → bag (bag (idx N)) → vec[ N ] ℕ → ℕ
nf+⟦ xss ⟧ γ = reduce [+] xss λ xs → nf*⟦ xs ⟧ γ

nf-𝕟 : ∀ {N} → ℕ → bag (bag (idx N))
nf-𝕟 Zero = zero
nf-𝕟 (Suc n) = b♭[ zero ] + nf-𝕟 n

postulate
  correct[nf-𝕟] : ∀ {N} (n : ℕ) (γ : vec[ N ] ℕ) → nf+⟦ nf-𝕟 {N} n ⟧ γ ≡ n

nf : ∀ {N} → exp N → bag (bag (idx N))
nf (Lit n) = nf-𝕟 n
nf (Var x) = b♭[ b♭[ x ] ]
nf (e₁ `+ e₂) = nf e₁ + nf e₂
nf (e₁ `* e₂) = nf e₁ * nf e₂

postulate
  correct[nf] : ∀ {N} (e : exp N) (γ : vec[ N ] ℕ) → nf+⟦ nf e ⟧ γ ≡ ⟦ e ⟧ γ


solve_[_≛_] : ∀ {N} (γ : vec[ N ] ℕ) (e₁ e₂ : exp N) {{_ : nf e₁ ≡ nf e₂}} → ⟦ e₁ ⟧ γ ≡ ⟦ e₂ ⟧ γ
solve γ [ e₁ ≛ e₂ ] {{ε}} rewrite sym (correct[nf] e₁ γ) | sym (correct[nf] e₂ γ) | ε = refl

-- a nontrivial arithmetic equality that is easily discharged by solve
_ : ∀ (x y z : ℕ) → x * (x + x + y + z) ≡ (y * x + z * 1 * x + x * 2 * x + 0) * 1 + 0
_ = λ x y z →
      let γ = [ x , y , z ]
          x = Var (𝕚 0)
          y = Var (𝕚 1)
          z = Var (𝕚 2)
      in
      solve γ
      [ x * (x + x + y + z)
      ≛ (y * x + z * Lit 1 * x + x * Lit 2 * x + Lit 0) * Lit 1 + Lit 0
      ]
