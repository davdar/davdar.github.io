-- Demo material that accompanies the talk:
-- Constructive Galois Connections: With Applications to Abstracting Gradual Typing
-- David Darais
-- Jan 13 2016, University of Chile
--
-- This is a demonstration of constructive Galois connections (Darais
-- and Van Horn, ArXiv 2015) applied to Abstracting Gradual Typing
-- (Garcia, Clark and Tanter, POPL 2016).
--
-- This demo requires no dependencies or standard library, and was
-- written using Agda 2.4.2.5.
-- 
-- Author: David Darais

module Demo where

---------------------
-- A Small Prelude --
---------------------

data _≡_ {𝓁} {A : Set 𝓁} (x : A) : A → Set 𝓁 where
  refl : x ≡ x

-- These tell Agda to use _≡_ as propositional equality during
-- dependent pattern matching and ≡-rewriting.

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

--------------
-- AGT Demo --
--------------

-- The precise type system
data type : Set where
  Anyᵖ : type
  Noneᵖ : type
  ⟨𝔹⟩ᵖ : type
  _⟨→⟩ᵖ_ : type → type → type

-- The precise metafunction that selects the domain of an arrow type
dom : type → type
dom (τ₁ ⟨→⟩ᵖ τ₂) = τ₁
dom τ = Noneᵖ

-- The precise equate operator where
--   equate τ₁ τ₂ = τ₁    𝑖𝑓 τ₁ = τ₂
--                  None  𝑖𝑓 τ₁ ≠ τ₂
equate : type → type → type
equate Anyᵖ Anyᵖ = Anyᵖ
equate Anyᵖ τ = Noneᵖ
equate Noneᵖ τ = Noneᵖ
equate ⟨𝔹⟩ᵖ ⟨𝔹⟩ᵖ = ⟨𝔹⟩ᵖ
equate ⟨𝔹⟩ᵖ τ = Noneᵖ
equate (τ₁₁ ⟨→⟩ᵖ τ₂₁) (τ₁₂ ⟨→⟩ᵖ τ₂₂) = equate τ₁₁ τ₁₂ ⟨→⟩ᵖ equate τ₂₁ τ₂₂
equate (τ₁ ⟨→⟩ᵖ τ₂) τ = Noneᵖ

-- The gradual type system
-- ?, the "unknown" type, is written as ⊤ᵍ because it is the top of
-- the precision lattice
data type♯ : Set where
  ⊤ᵍ : type♯
  Anyᵍ : type♯
  Noneᵍ : type♯
  ⟨𝔹⟩ᵍ : type♯
  _⟨→⟩ᵍ_ : type♯ → type♯ → type♯

-- The partial ordering relation on gradual types
data _⊑_ : type♯ → type♯ → Set where
  ⊤ᵒ : ∀ {τ} → τ ⊑ ⊤ᵍ
  Anyᵒ : Anyᵍ ⊑ Anyᵍ
  Noneᵒ : Noneᵍ ⊑ Noneᵍ
  ⟨𝔹⟩ᵒ : ⟨𝔹⟩ᵍ ⊑ ⟨𝔹⟩ᵍ
  _⟨→⟩ᵒ_ : ∀ {τ₁₁ τ₂₁ τ₁₂ τ₂₂}
    → τ₁₁ ⊑ τ₁₂
    → τ₂₁ ⊑ τ₂₂
    → (τ₁₁ ⟨→⟩ᵍ τ₂₁) ⊑ (τ₁₂ ⟨→⟩ᵍ τ₂₂)

-- The constructive abstraction function (like α)
η : type → type♯
η Anyᵖ = Anyᵍ
η Noneᵖ = Noneᵍ
η ⟨𝔹⟩ᵖ = ⟨𝔹⟩ᵍ
η (τ₁ ⟨→⟩ᵖ τ₂) = η τ₁ ⟨→⟩ᵍ η τ₂

-- The constructive concretization function, written as a relation
data _∈γ[_] : type → type♯ → Set where
  ⊤ᶜ : ∀ {τ} → τ ∈γ[ ⊤ᵍ ]
  Anyᶜ : Anyᵖ ∈γ[ Anyᵍ ]
  Noneᶜ : Noneᵖ ∈γ[ Noneᵍ ]
  ⟨𝔹⟩ᶜ : ⟨𝔹⟩ᵖ ∈γ[ ⟨𝔹⟩ᵍ ]
  _⟨→⟩ᶜ_ : ∀ {τ₁ τ₂ τ₁♯ τ₂♯}
    → τ₁ ∈γ[ τ₁♯ ]
    → τ₂ ∈γ[ τ₂♯ ]
    → (τ₁ ⟨→⟩ᵖ τ₂) ∈γ[ τ₁♯ ⟨→⟩ᵍ τ₂♯ ]

-- Soundness for the constructive Galois connection η⇄γ
sound[ηγ] : ∀ τ → τ ∈γ[ η τ ]
sound[ηγ] Anyᵖ = Anyᶜ
sound[ηγ] Noneᵖ = Noneᶜ
sound[ηγ] ⟨𝔹⟩ᵖ = ⟨𝔹⟩ᶜ
sound[ηγ] (τ₁ ⟨→⟩ᵖ τ₂) = sound[ηγ] τ₁ ⟨→⟩ᶜ sound[ηγ] τ₂

-- Completeness for the constructive Galois connection η⇄γ
complete[ηγ] : ∀ {τ τ♯} → τ ∈γ[ τ♯ ] → η τ ⊑ τ♯
complete[ηγ] ⊤ᶜ = ⊤ᵒ
complete[ηγ] Anyᶜ = Anyᵒ
complete[ηγ] Noneᶜ = Noneᵒ
complete[ηγ] ⟨𝔹⟩ᶜ = ⟨𝔹⟩ᵒ
complete[ηγ] (∈γ₁ ⟨→⟩ᶜ ∈γ₂) =  complete[ηγ] ∈γ₁ ⟨→⟩ᵒ complete[ηγ] ∈γ₂

-- The gradual metafunction that selects the domain of an arrow type
dom♯ : type♯ → type♯
dom♯ ⊤ᵍ = ⊤ᵍ
dom♯ (τ₁ ⟨→⟩ᵍ τ₂) = τ₁
dom♯ τᵍ = Noneᵍ

-- The proof of correctness of dom♯ in the constructive Galois
-- connection framework
correct[dom♯] : ∀ τ → η (dom τ) ≡ dom♯ (η τ)
correct[dom♯] Anyᵖ = refl
correct[dom♯] Noneᵖ = refl
correct[dom♯] ⟨𝔹⟩ᵖ = refl
correct[dom♯] (τ₁ ⟨→⟩ᵖ τ₂) = refl

-- The gradual equate operator
equate♯ : type♯ → type♯ → type♯
equate♯ ⊤ᵍ τ = τ
equate♯ τ ⊤ᵍ = τ
equate♯ Anyᵍ Anyᵍ = Anyᵍ
equate♯ Anyᵍ τ = Noneᵍ
equate♯ Noneᵍ τ = Noneᵍ
equate♯ ⟨𝔹⟩ᵍ ⟨𝔹⟩ᵍ = ⟨𝔹⟩ᵍ
equate♯ ⟨𝔹⟩ᵍ τ = Noneᵍ
equate♯ (τ₁₁ ⟨→⟩ᵍ τ₂₁) (τ₁₂ ⟨→⟩ᵍ τ₂₂) = equate♯ τ₁₁ τ₁₂ ⟨→⟩ᵍ equate♯ τ₂₁ τ₂₂
equate♯ (τ₁ ⟨→⟩ᵍ τ₂) τ = Noneᵍ

-- The proof of correctness of equate♯ in the constructive Galois
-- connection framework
--
-- A much simpler proof for this exists which requires redefining
-- equate♯ to have more structure in its definition. Brute-force
-- enumerating all cases is sufficient for now.
correct[equate♯] : ∀ τ₁ τ₂ → η (equate τ₁ τ₂) ≡ equate♯ (η τ₁) (η τ₂)
correct[equate♯] Anyᵖ Anyᵖ = refl
correct[equate♯] Anyᵖ Noneᵖ = refl
correct[equate♯] Anyᵖ ⟨𝔹⟩ᵖ = refl
correct[equate♯] Anyᵖ (τ₁ ⟨→⟩ᵖ τ₂) = refl
correct[equate♯] Noneᵖ Anyᵖ = refl
correct[equate♯] Noneᵖ Noneᵖ = refl
correct[equate♯] Noneᵖ ⟨𝔹⟩ᵖ = refl
correct[equate♯] Noneᵖ (τ₁ ⟨→⟩ᵖ τ₂) = refl
correct[equate♯] ⟨𝔹⟩ᵖ Anyᵖ = refl
correct[equate♯] ⟨𝔹⟩ᵖ Noneᵖ = refl
correct[equate♯] ⟨𝔹⟩ᵖ ⟨𝔹⟩ᵖ = refl
correct[equate♯] ⟨𝔹⟩ᵖ (τ₁ ⟨→⟩ᵖ τ₂) = refl
correct[equate♯] (τ₁ ⟨→⟩ᵖ τ₂) Anyᵖ = refl
correct[equate♯] (τ₁ ⟨→⟩ᵖ τ₂) Noneᵖ = refl
correct[equate♯] (τ₁ ⟨→⟩ᵖ τ₂) ⟨𝔹⟩ᵖ = refl
correct[equate♯] (τ₁₁ ⟨→⟩ᵖ τ₂₁) (τ₁₂ ⟨→⟩ᵖ τ₂₂) rewrite correct[equate♯] τ₁₁ τ₁₂ | correct[equate♯] τ₂₁ τ₂₂ = refl

-- Exercises:
-- 
-- * Easy: Define the subtyping relation <: on precise types.
-- * Moderate: Define the subtyping relation <:♯ on gradual types.
-- * Hard: Prove the subtyping relation <:♯ correct using η and/or γ.
--
-- * Moderate: Define ∨: and ∧:, the join and meet for the subtyping relation <: on precise types.
-- * Hard: Define ∨:♯ and ∧:♯, the join and meet for the subtyping relation <:♯ on gradual types.
-- * Very Hard: Prove ∨:♯ and ∧:♯ correct using η and/or γ.
--
-- * Very Hard: Define a term language and substitution operation for
--   the precise language, and show that the subtyping relation <: is
--   safe for substitution.
-- * Very Hard: Define a term language and substitution operation for
--   the gradual language (in AGT style), and show that the abstract
--   subtyping relation <:♯ is safe for substitution.
-- * Very Hard: Prove substitution in the gradual language correct as
--   an abstraction of precise substitution.
