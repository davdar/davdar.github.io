module IC6 where

-- UNICODE --

{-
    ¬    \not
    ∧    \and
    ∨    \or
    ∃    \ex
    ₁    \_1
    ₂    \_2
    ⦂     \o:
    •    \bu
    𝟙    \bb1
    𝟘    \bb0
-}

-- LIB --

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

◇ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
◇ ↯ = ↯

infixl 8 _⊚_
_⊚_ : ∀ {A : Set} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
↯ ⊚ ↯ = ↯

-- ⌄⌄⌄⌄⌄⌄⌄⌄ --
-- IN CLASS --
-- ⌄⌄⌄⌄⌄⌄⌄⌄ --

-- cartesian product --

infix 6 _∧_
data _∧_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A ∧ B

π₁ : ∀ {A B : Set} → A ∧ B → A
π₁ ⟨ x , y ⟩ = x

π₂ : ∀ {A B : Set} → A ∧ B → B
π₂ ⟨ x , y ⟩ = y

η[∧] : ∀ {A B : Set} (xy : A ∧ B) → ⟨ π₁ xy , π₂ xy ⟩ ≡ xy
η[∧] ⟨ x , y ⟩ = ↯

-- disjoint union --

infix 5 _∨_
data _∨_ (A B : Set) : Set where
  Inl : A → A ∨ B
  Inr : B → A ∨ B

case : ∀ {A B C : Set} → A ∨ B → (A → C) → (B → C) → C
case (Inl x) f g = f x
case (Inr y) f g = g y

η[∨] : ∀ {A B : Set} (xy : A ∨ B) → case xy Inl Inr ≡ xy
η[∨] (Inl x) = ↯
η[∨] (Inr x) = ↯

-- singleton set --

data 𝟙 : Set where
  • : 𝟙

η[𝟙] : ∀ (x : 𝟙) → x ≡ •
η[𝟙] • = ↯

-- empty set --

data 𝟘 : Set where

absurd : ∀ {A : Set} → 𝟘 → A
absurd ()

η[𝟘] : ∀ {A : Set} (f : 𝟘 → A) (x : 𝟘) → f x ≡ absurd x
η[𝟘] f ()

-- negation --

infixr 21 ¬_
¬_ : Set → Set
¬ A = A → 𝟘

-- functions --

-- exponentiation is the function space flipped
-- A ^^ B ≜ B → A

_^^_ : Set → Set → Set
A ^^ B = B → A

η[^^] : ∀ {A B : Set} (f : A ^^ B) → (λ (x : B) → f x) ≡ f
η[^^] f = {!↯!}

postulate
  ext : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

-- do existentials? --

data existential (A : Set) (B : A → Set) : Set where
  ⟨∃_,_⟩ : ∀ (x : A) → B x → existential A B

-- m × n ≡ n × m
--
-- A ∧ B ⇄ B ∧ A
--
-- A ∧ B → B ∧ A  (to)
-- B ∧ A → A ∧ B  (fr)
-- if (x : A ∧ B) then (fr (to x)) ≡ x (frto)
-- if (y : B ∧ B) then (to (fr y)) ≡ y (tofr)

   


-- commutativity of ∧ --

commu[∧]-to : ∀ {A B : Set} → A ∧ B → B ∧ A
commu[∧]-to ⟨ x , y ⟩ = ⟨ y , x ⟩

commu[∧]-fr : ∀ {A B : Set} → B ∧ A → A ∧ B
commu[∧]-fr ⟨ y , x ⟩ = ⟨ x , y ⟩

commu[∧]-frto : ∀ {A B : Set} (xy : A ∧ B) → commu[∧]-fr (commu[∧]-to xy) ≡ xy
commu[∧]-frto ⟨ x , y ⟩ = ↯

commu[∧]-tofr : ∀ {A B : Set} (yx : B ∧ A) → commu[∧]-to (commu[∧]-fr yx) ≡ yx
commu[∧]-tofr ⟨ y , x ⟩ = ↯

-- associativity of ∧ --

assoc[∧]-to : ∀ {A B C : Set} → (A ∧ B) ∧ C → A ∧ (B ∧ C)
assoc[∧]-to ⟨ ⟨ x , y ⟩ , z ⟩ = ⟨ x , ⟨ y , z ⟩ ⟩

assoc[∧]-fr : ∀ {A B C : Set} → A ∧ (B ∧ C) → (A ∧ B) ∧ C
assoc[∧]-fr xyz = {!!}

assoc[∧]-frto : ∀ {A B C  : Set} (xyz : (A ∧ B) ∧ C) → assoc[∧]-fr (assoc[∧]-to xyz) ≡ xyz
assoc[∧]-frto xyz = {!!}

assoc[∧]-tofr : ∀ {A B C  : Set} (xyz : A ∧ (B ∧ C)) → assoc[∧]-to (assoc[∧]-fr xyz) ≡ xyz
assoc[∧]-tofr xyz = {!!}

-- left-unit of ∧ --

lunit[∧]-to : ∀ {A : Set} → 𝟙 ∧ A → A
lunit[∧]-to ox = π₂ ox

lunit[∧]-fr : ∀ {A : Set} → A → 𝟙 ∧ A 
lunit[∧]-fr x = ⟨ • , x ⟩

lunit[∧]-frto : ∀ {A : Set} (xy : 𝟙 ∧ A) → lunit[∧]-fr (lunit[∧]-to xy) ≡ xy
lunit[∧]-frto ⟨ • , x ⟩ = ↯

lunit[∧]-tofr : ∀ {A : Set} (x : A) → lunit[∧]-to (lunit[∧]-fr x) ≡ x
lunit[∧]-tofr x = {!!}

-- commutativity of ∨ --

commu[∨]-to : ∀ {A B : Set} → A ∨ B → B ∨ A
commu[∨]-to xy = {!!}

commu[∨]-fr : ∀ {A B : Set} → B ∨ A → A ∨ B
commu[∨]-fr xy = {!!}

commu[∨]-frto : ∀ {A B : Set} (xy : A ∨ B) → commu[∨]-fr (commu[∨]-to xy) ≡ xy
commu[∨]-frto xy = {!!}

commu[∨]-tofr : ∀ {A B : Set} (xy : B ∨ A) → commu[∨]-to (commu[∨]-fr xy) ≡ xy
commu[∨]-tofr xy = {!!}

-- associativity of ∨ --

assoc[∨]-to : ∀ {A B C : Set} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
assoc[∨]-to (Inl (Inl x)) = Inl x
assoc[∨]-to (Inl (Inr y)) = Inr (Inl y)
assoc[∨]-to (Inr z) = Inr (Inr z)

assoc[∨]-fr : ∀ {A B C : Set} → A ∨ (B ∨ C) → (A ∨ B) ∨ C
assoc[∨]-fr xyz = {!!}

assoc[∨]-frto : ∀ {A B C  : Set} (xyz : (A ∨ B) ∨ C) → assoc[∨]-fr (assoc[∨]-to xyz) ≡ xyz
assoc[∨]-frto xyz = {!!}

assoc[∨]-tofr : ∀ {A B C  : Set} (xyz : A ∨ (B ∨ C)) → assoc[∨]-to (assoc[∨]-fr xyz) ≡ xyz
assoc[∨]-tofr xyz = {!!}

-- left-unit of ∨ --

-- 0 + m ≡ m

-- 𝟘 ∨ A ⇄ A

lunit[∨]-to : ∀ {A : Set} → 𝟘 ∨ A → A
lunit[∨]-to (Inl ())
lunit[∨]-to (Inr x) = x

lunit[∨]-fr : ∀ {A : Set} → A → 𝟘 ∨ A 
lunit[∨]-fr x = Inr x

lunit[∨]-frto : ∀ {A : Set} (xy : 𝟘 ∨ A) → lunit[∨]-fr (lunit[∨]-to xy) ≡ xy
lunit[∨]-frto ox = {!!}

lunit[∨]-tofr : ∀ {A : Set} (x : A) → lunit[∨]-to (lunit[∨]-fr x) ≡ x
lunit[∨]-tofr x = {!!}

-- left-zero of ∧ --

-- 0 × m ≡ 0
--
-- 𝟘 ∧ A ⇄ 𝟘

lzero[∧]-to : ∀ {A : Set} → 𝟘 ∧ A → 𝟘
lzero[∧]-to ox = {!!}

lzero[∧]-fr : ∀ {A : Set} → 𝟘 → 𝟘 ∧ A
lzero[∧]-fr x = {!!}

lzero[∧]-frto : ∀ {A : Set} (xy : 𝟘 ∧ A) → lzero[∧]-fr (lzero[∧]-to xy) ≡ xy
lzero[∧]-frto ox = {!!}

lzero[∧]-tofr : ∀ {A : Set} (x : 𝟘) → lzero[∧]-to {A = A} (lzero[∧]-fr x) ≡ x
lzero[∧]-tofr x = {!!}

-- left-distributivity of ∧ --

ldist[∧]-to : ∀ {A B C : Set} → (A ∨ B) ∧ C → (A ∧ C) ∨ (B ∧ C)
ldist[∧]-to xyz = {!!}

ldist[∧]-fr : ∀ {A B C : Set} → (A ∧ C) ∨ (B ∧ C) → (A ∨ B) ∧ C 
ldist[∧]-fr xzyz = {!!}

ldist[∧]-frto : ∀ {A B C : Set} (xyz : (A ∨ B) ∧ C) → ldist[∧]-fr (ldist[∧]-to xyz) ≡ xyz
ldist[∧]-frto xyz = {!!}

ldist[∧]-tofr : ∀ {A B C : Set} (xzyz : (A ∧ C) ∨ (B ∧ C) ) → ldist[∧]-to (ldist[∧]-fr xzyz) ≡ xzyz
ldist[∧]-tofr xzyz = {!!}

-- Q: what about:
--
-- (A ∧ B) ∨ C ≈ (A ∨ C) ∧ (B ∨ C)
--
-- would correspond to
-- (m × n) + p ≟ (m + p) × (n + p)

ldist[∨]-to : ∀ {A B C : Set} → (A ∧ B) ∨ C → (A ∨ C) ∧ (B ∨ C)
ldist[∨]-to (Inl ⟨ x , y ⟩) = ⟨ (Inl x) , (Inl y) ⟩
ldist[∨]-to (Inr z) = ⟨ (Inr z) , (Inr z) ⟩

ldist[∨]-fr : ∀ {A B C : Set} → (A ∨ C) ∧ (B ∨ C) → (A ∧ B) ∨ C
ldist[∨]-fr ⟨ Inl x , Inl x₁ ⟩ = {!!}
ldist[∨]-fr ⟨ Inl x , Inr x₁ ⟩ = {!!}
ldist[∨]-fr ⟨ Inr x , Inl x₁ ⟩ = {!!}
ldist[∨]-fr ⟨ Inr x , Inr x₁ ⟩ = {!!}

ldist[∨]-frto : ∀ {A B C : Set} (xyz : (A ∧ B) ∨ C) → ldist[∨]-fr (ldist[∨]-to xyz) ≡ xyz
ldist[∨]-frto xyz = {!!}

ldist[∨]-tofr : ∀ {A B C : Set} (xzyz : (A ∨ C) ∧ (B ∨ C)) → ldist[∨]-to (ldist[∨]-fr xzyz) ≡ xzyz
ldist[∨]-tofr xyzy = {!!}

-- associativity* of ^^ --

-- (A ^^ B) ^^ C ≈ A ^^ (C ∧ B)
-- ==
-- C → (B → A) ≈ (C ∧ B) → A

assoc[^^]-to : ∀ {A B C : Set} → (A ^^ B) ^^ C → A ^^ (B ∧ C)
assoc[^^]-to f yz = {!!}

assoc[^^]-fr : ∀ {A B C : Set} → A ^^ (B ∧ C) → (A ^^ B) ^^ C
assoc[^^]-fr f z y = {!!}

assoc[^^]-frto : ∀ {A B C : Set} (f : (A ^^ B) ^^ C) → assoc[^^]-fr (assoc[^^]-to f) ≡ f
assoc[^^]-frto f = {!!}

assoc[^^]-tofr-ext : ∀ {A B C : Set} (f : A ^^ (B ∧ C)) (yz : B ∧ C) → assoc[^^]-to (assoc[^^]-fr f) yz ≡ f yz
assoc[^^]-tofr-ext f yz = {!!}

assoc[^^]-tofr : ∀ {A B C : Set} (f : A ^^ (B ∧ C)) → assoc[^^]-to (assoc[^^]-fr f) ≡ f
assoc[^^]-tofr f = {!!}

-- A ^^ (B ∨ C) ≈ (A ^^ B) ∧ (A ^^ C)
-- (B ∨ C → A) ≈ (B → A) ∧ (C → A)
-- TODO

-- (A ∧ B) ^^ C ≈ (A ^^ C) ∧ (B ^^ C)
-- (C → (A ∧ B)) ≈ (C → A) ∧ (C → B)
-- TODO
