module la19 where

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
_ = V[ 1 , 2 , 3 , 4 ]

matrix[_,_] : ℕ → ℕ → Set → Set
matrix[ m , n ] A = vec[ m ] (vec[ n ] A)

_ : matrix[ 2 , 3 ] ℕ
_ = V[ V[ 1 , 2 , 3 ]
     , V[ 4 , 5 , 6 ]
     ]

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
  const[ Zero ] x = []
  const[ Suc n ] x = x ∷ const[ n ] x

  _[_] : ∀ {n} → vec[ n ] A → idx n → A
  (x ∷ xs) [ Zero ] = x
  (x ∷ xs) [ Suc ι ] = xs [ ι ]

  _[_↦_] : ∀ {n} → vec[ n ] A → idx n → A → vec[ n ] A
  (x ∷ xs) [ Zero ↦ x′ ] = x′ ∷ xs
  (x ∷ xs) [ Suc ι ↦ x′ ] = x ∷ (xs [ ι ↦ x′ ])

  vec-iter : ∀ {B : Set} {n} → vec[ n ] A → B → (idx n → A → B → B) → B
  vec-iter [] i f = i
  vec-iter (x ∷ xs) i f = vec-iter xs (f Zero x i) λ ι x y → f (Suc ι) x y

_ : const[ 3 ] 2 ≡ V[ 2 , 2 , 2 ]
_ = refl

_ : V[ 1 , 2 , 3 ] [ 𝕟2 ] ≡ 3
_ = refl

_ : V[ 1 , 2 , 3 ] [ 𝕟2 ↦ 4 ] ≡ V[ 1 , 2 , 4 ]
_ = refl

-- graphs --

graph : ℕ → Set
graph n = matrix[ n , n ] 𝔹

{-# TERMINATING #-}
dfs′ : ∀ {n} → idx n → graph n → vec[ n ] 𝔹 → list (idx n) ∧ vec[ n ] 𝔹
dfs′ ι₀ G S with S [ ι₀ ]
… | I = ⟨ [] , S ⟩
… | O = vec-iter (G [ ι₀ ]) ⟨ L[ ι₀ ] , S [ ι₀ ↦ I ] ⟩ λ where
  ι O ⟨ xs , S′ ⟩ → ⟨ xs , S′ ⟩
  ι I ⟨ xs , S′ ⟩ → 
    let ⟨ xs′ , S″ ⟩ = dfs′ ι G S′
    in ⟨ xs ++ xs′ , S″ ⟩

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
_ = refl
