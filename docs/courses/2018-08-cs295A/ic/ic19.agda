module ic19 where

open import Basics-v5

-- vectors --

syntax vec A n = vec[ n ] A
data vec (A : Set) : ℕ → Set where
  [] : vec[ 0 ] A
  _∷_ : ∀ {n} → A → vec[ n ] A → vec[ Suc n ] A

pattern V[_] a = a ∷ []
pattern V[_,_] a b = a ∷ V[ b ]
pattern V[_,_,_] a b c = a ∷ V[ b , c ]
pattern V[_,_,_,_] a b c d = a ∷ V[ b , c , d ]
pattern V[_,_,_,_,_] a b c d e = a ∷ V[ b , c , d , e ]
pattern V[_,_,_,_,_,_] a b c d e f = a ∷ V[ b , c , d , e , f ]
pattern V[_,_,_,_,_,_,_] a b c d e f g = a ∷ V[ b , c , d , e , f , g ]
pattern V[_,_,_,_,_,_,_,_] a b c d e f g h = a ∷ V[ b , c , d , e , f , g , h ]
pattern V[_,_,_,_,_,_,_,_,_] a b c d e f g h i = a ∷ V[ b , c , d , e , f , g , h , i ]
pattern V[_,_,_,_,_,_,_,_,_,_] a b c d e f g h i j = a ∷ V[ b , c , d , e , f , g , h , i , j ]

_ : vec[ 4 ] ℕ
_ = {!!}

matrix[_,_] : ℕ → ℕ → Set → Set
matrix[ m , n ] A = {!!}

_ : matrix[ 2 , 3 ] ℕ
_ = {!!}

data idx : ℕ → Set where
  Zero : ∀ {n} → idx (Suc n)
  Suc : ∀ {n} → idx n → idx (Suc n)

pattern 𝕟0 = Zero
pattern 𝕟1 = Suc 𝕟0
pattern 𝕟2 = Suc 𝕟1
pattern 𝕟3 = Suc 𝕟2
pattern 𝕟4 = Suc 𝕟3
pattern 𝕟5 = Suc 𝕟4
pattern 𝕟6 = Suc 𝕟5
pattern 𝕟7 = Suc 𝕟6
pattern 𝕟8 = Suc 𝕟7
pattern 𝕟9 = Suc 𝕟8
pattern 𝕟10 = Suc 𝕟9

𝕟 : ∀ (n : ℕ) {m : ℕ} {{_ : n <? m ≡ LT}} → idx m
𝕟 Zero {Zero} ⦃ () ⦄
𝕟 Zero {Suc m} ⦃ ε ⦄ = Zero
𝕟 (Suc n) {Zero} ⦃ () ⦄
𝕟 (Suc n) {Suc m} ⦃ ε ⦄ = Suc (𝕟 n)

_ : let n₁ : idx 20
        n₁ = 𝕟 9
        n₂ : idx 20
        n₂ = 𝕟9
    in n₁ ≡ n₂
_ = refl

pattern I = True
pattern O = False

module _ {A : Set} where

  const[_] : ∀ n → A → vec[ n ] A
  const[ n ] x = {!!}

  _[_] : ∀ {n} → vec[ n ] A → idx n → A
  xs [ n ] = {!!}

  _[_↦_] : ∀ {n} → vec[ n ] A → idx n → A → vec[ n ] A
  xs [ n ↦ x′ ] = {!!}

  vec-iter : ∀ {B : Set} {n} → vec[ n ] A → B → (idx n → A → B → B) → B
  vec-iter xs i f = {!!}

_ : const[ 3 ] 2 ≡ V[ 2 , 2 , 2 ]
_ = {!!}

_ : V[ 1 , 2 , 3 ] [ 𝕟2 ] ≡ 3
_ = {!!}

_ : V[ 1 , 2 , 3 ] [ 𝕟2 ↦ 4 ] ≡ V[ 1 , 2 , 4 ]
_ = {!!}

-- graphs --

graph : ℕ → Set
graph n = {!!}

{-# TERMINATING #-}
dfs′ : ∀ {n} → idx n → graph n → vec[ n ] 𝔹 → list (idx n) ∧ vec[ n ] 𝔹
dfs′ ι₀ G S = {!!}

dfs : ∀ {n} → graph n → idx n → list (idx n)
dfs G ι =
  let ⟨ xs , _ ⟩ = dfs′ ι G (const[ _ ] O)
  in xs

-- 0 -> 1
-- 0 -> 3
-- 1 -> 4
-- 2 -> 1
-- 2 -> 4
-- 3 -> 0
-- 3 -> 2
-- 4 -> 0
G1 : graph 5
G1 = V[ V[ O , I , O , I , O ]
      , V[ O , O , O , O , I ]
      , V[ O , I , O , O , I ]
      , V[ I , O , I , O , O ]
      , V[ I , O , O , O , O ]
      ]

_ : dfs G1 Zero ≡ L[ 𝕟0 , 𝕟1 , 𝕟4 , 𝕟3 , 𝕟2 ]
_ = {!!}

-------------------------
-- final project ideas --
-------------------------

{-

- real numbers and √2

- Tic tac toe

- Lattice theory and fixpoints (Knaster-Tarski): https://en.wikipedia.org/wiki/Knaster–Tarski_theorem

- Time complexity (e.g., of sorting, O(n log n))

- trie data structure (https://en.wikipedia.org/wiki/Trie)

- Random number generators (https://en.wikipedia.org/wiki/Pseudorandom_number_generator)

-}
