{-
Name: ⁇
Date: ⁇

Collaboration Statement:
«Write your collaboration statement here…»
-}

---------------
-- LOGISTICS --
---------------

-- To submit the assignment, upload your solution to blackboard as a
-- single .agda file.
--
-- Make sure you write your name, the date, and your collaboration
-- statement above, as indicated by the course course collaboration
-- policy:
--
--     Collaboration on the high-level ideas and approach on
--     assignments is encouraged. Copying someone else's work is not
--     allowed. Any collaboration, even at a high level, must be
--     declared when you submit your assignment. Every assignment must
--     include a collaboration statement. E.g., "I discussed
--     high-level strategies for solving problem 2 and 5 with Alex."
--     Students caught copying work are eligible for immediate failure
--     of the course and disciplinary action by the University. All
--     academic integrity misconduct will be treated according to
--     UVM's Code of Academic Integrity.
--
-- This assignment consists of a LIB section which contains relevant
-- definitions and lemmas which you should refer to throughout the
-- assignment, and an ASSIGNMENT section which contains definitions
-- and lemmas with “holes” in them. *If you only change the code
-- within the holes and your entire assignment compiles without
-- errors, you are guaranteed 100% on the assignment.*

module hw3 where

---------
-- LIB --
---------

infix 4 _≡_
infixl 6 _+_ _∸_
infixl 7 _*_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n     =  zero
(suc m) * n  =  n + (m * n)

_∸_ : ℕ → ℕ → ℕ
m       ∸ zero     =  m
zero    ∸ (suc n)  =  zero
(suc m) ∸ (suc n)  =  m ∸ n

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ}
    --------------
    → zero ≤ n
  suc : ∀ {m n : ℕ}
    → m ≤ n
    -----------------
    → suc m ≤ suc n

infixr 2 _×_
data _×_ : Set → Set → Set where
  ⟨_,_⟩ : ∀ {A B : Set}
    → A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

infix 1 _⊎_
data _⊎_ : Set → Set → Set where
  inj₁ : ∀ {A B : Set}
    → A
      -----
    → A ⊎ B

  inj₂ : ∀ {A B : Set}
    → B
      -----
    → A ⊎ B

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

_≢_ : ∀ {A : Set} (x y : A) → Set
x ≢ y = ¬ x ≡ y

infix 2 ∃
syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B
data ∃ (A : Set) (B : A → Set) : Set where
  ⟨∃_,_⟩ : (x : A) → B x → ∃ A B

postulate
  -- + --
  +-runit : ∀ (m : ℕ) → m + zero ≡ m
  +-rsuc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-assoc : ∀ (m n p : ℕ) → m + n + p ≡ m + (n + p)
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  -- * --
  *-rzero : ∀ (m : ℕ) → m * zero ≡ zero
  *-runit : ∀ (m : ℕ) → m * 1 ≡ m
  *-rsuc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
  *-assoc : ∀ (m n p : ℕ) → m * n * p ≡ m * (n * p)
  *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
  -- ≤ --
  ≤-refl : ∀ (m : ℕ) → m ≤ m
  ≤-trans : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
  ≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

----------------
-- ASSIGNMENT --
----------------

-- Prove that negation distributes through sums
-- i.e., that (¬ (A ⊎ B)) and (¬ A × ¬ B) are isomorphic

-- E1: [★]
-- The "to" mapping
¬-⊎-dist-L : ∀ {A B : Set} → ¬ (A ⊎ B) → ¬ A × ¬ B
¬-⊎-dist-L ¬xy = {!!}

-- E2: [★]
-- The "from" mapping
¬-⊎-dist-R : ∀ {A B : Set} → ¬ A × ¬ B → ¬ (A ⊎ B)
¬-⊎-dist-R ¬xy = {!!}

-- E3 : [★]
-- The extensional "to ∘ from" round trip law
¬-⊎-dist-iso-R-ext : ∀ {A B : Set} (¬xy : ¬ (A ⊎ B)) (xy : A ⊎ B) → ¬-⊎-dist-R (¬-⊎-dist-L ¬xy) xy ≡ ¬xy xy
¬-⊎-dist-iso-R-ext ¬xy = {!!}

-- E4 : [★★]
-- The functional "to ∘ from" found trip law
-- HINT: use the extensionality postulate and the previous lemma
¬-⊎-dist-iso-R : ∀ {A B : Set} (¬xy : ¬ (A ⊎ B)) → ¬-⊎-dist-R (¬-⊎-dist-L ¬xy) ≡ ¬xy 
¬-⊎-dist-iso-R ¬xy = {!!}

-- E5: [★]
-- The "from ∘ to" round trip law
¬-⊎-dist-iso-L : ∀ {A B : Set} (¬xy : ¬ A × ¬ B) → ¬-⊎-dist-L (¬-⊎-dist-R ¬xy) ≡ ¬xy 
¬-⊎-dist-iso-L ¬xy = {!!}

-- E6: [★]
-- Prove that negation distributes through products
-- Just prove the "from mapping
-- (The "to mapping is true logically, but not computationally derivable)
¬-×-dist-R : ∀ {A B : Set} → ¬ A ⊎ ¬ B → ¬ (A × B)
¬-×-dist-R ¬xy xy = {!!}

-- Prove that negation distributes through existentials

-- E7: [★★]
-- The "to" mapping
¬-∃-dist-L : ∀ {A : Set} {B : A → Set} → ¬ (∃[ x ∈ A ] B x) → (∀ (x : A) → ¬ (B x))
¬-∃-dist-L ¬y[x] x y[x] = {!!}

-- E8: [★★]
-- The "from" mapping
¬-∃-dist-R : ∀ {A : Set} {B : A → Set} → (∀ (x : A) → ¬ (B x)) → ¬ (∃[ x ∈ A ] B x)
¬-∃-dist-R ¬y[x] y[x] = {!!}

-- E9: [★★]
-- Prove that negation distributes through universal quanitifers
-- Just prove the "from mapping
-- (The "to mapping is true logically, but not computationally derivable)
¬-∀-dist-R : ∀ {A : Set} {B : A → Set} → ∃[ x ∈ A ] ¬ (B x) → ¬ (∀ (x : A) → B x)
¬-∀-dist-R ¬y[x] y[x] = {!!}
