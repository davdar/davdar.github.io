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

module hw5 where

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

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ}
    --------------
    → zero < suc n
  suc : ∀ {m n : ℕ}
    → m < n
    -----------------
    → suc m < suc n

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

data 𝔹 : Set where
  true  : 𝔹
  false : 𝔹

infixr 5 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

pattern [_] a = a ∷ []
pattern [_,_] a b = a ∷ [ b ]
pattern [_,_,_] a b c = a ∷ [ b , c ]
pattern [_,_,_,_] a b c d = a ∷ [ b , c , d ]
pattern [_,_,_,_,_] a b c d e = a ∷ [ b , c , d , e ]
pattern [_,_,_,_,_,_] a b c d e f = a ∷ [ b , c , d , e , f ]
pattern [_,_,_,_,_,_,_] a b c d e f g = a ∷ [ b , c , d , e , f , g ]
pattern [_,_,_,_,_,_,_,_] a b c d e f g h = a ∷ [ b , c , d , e , f , g , h ]
pattern [_,_,_,_,_,_,_,_,_] a b c d e f g h i = a ∷ [ b , c , d , e , f , g , h , i ]
pattern [_,_,_,_,_,_,_,_,_,_] a b c d e f g h i j = a ∷ [ b , c , d , e , f , g , h , i , j ]

infixl 6 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

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
  -- lists --
  ++-runit : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
  ++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

----------------
-- ASSIGNMENT --
----------------

-- E1: [★]
-- Write a function that compares two natural numbers `m` and `n`, and
-- returns true if `m` is strictly less than `n`, and false if `m` is
-- equal to or greater than `n`.
_<?_ : ℕ → ℕ → 𝔹
m <? n = {!!}

-- E2: [★]
-- Verify one direction of correctness for `_<?_`: if `m` is strictly
-- less than `n`, then `m <? n` returns true
-- HINT: do induction on the evidence that `m < n`
cor[<?]-L : ∀ {m n : ℕ} → m < n → m <? n ≡ true
cor[<?]-L ε = {!!}

-- E3: [★]
-- Verify the other direction of correctness for `_<?_`: if `m <? n`
-- returns true, then `m` is strictly less than `n`.
-- HINT: do induction on `m` and `n`
cor[<?]-R : ∀ (m n : ℕ) → m <? n ≡ true → m < n
cor[<?]-R m n ε = {!!}

-- E4: [★]
-- Write a function that compares two natural numbers `m` and `n`, and
-- returns true if the numbers are the same, and false if the numbers
-- are different.
_≡?_ : ℕ → ℕ → 𝔹
m ≡? n = {!!}

-- E5: [★★]
-- Verify one direction of correctness for `_≡?_`: if `m` and `n` are
-- equal, then `m ≡? n` returns true.
-- HINT: do induction on `m` and `n`
cor[≡?]-L : ∀ (m n : ℕ) → m ≡ n → (m ≡? n ≡ true)
cor[≡?]-L m n ε = {!!}

-- E6: [★]
-- Verify the other direction of correctness for `_≡?_`: if `m ≡? n`
-- returns true, then `m` and `n` are equal.
-- HINT: do induction on `m` and `n`
cor[≡?]-R : ∀ (m n : ℕ) → (m ≡? n ≡ true) → m ≡ n
cor[≡?]-R m n ε = {!!}

-- E7: [★★★]
-- Prove that if you reverse the concatenation of two lists, it's the
-- same as concatenating the reversal of each list (in reverse order)
-- HINT: do induction on `xs`; use ++-runit and ++-assoc
reverse-++-dist : ∀ {A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-dist xs ys = {!!}

-- E8: [★★]
-- Prove that if you reverse a list twice, you get the list you
-- started with.
-- HINT: do induction on `xs`; use reverse-++-dist
reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive xs = {!!}

-- E9: [★★]
-- Prove that if you map the composition of functions, it is the same
-- as composing the map of those functions
-- HINT: do induction on xs
map-∘-dist : ∀ {A B C : Set} (g : B → C) (f : A → B) (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-∘-dist g f xs = {!!}

-- E10: [★★]
-- Prove that if you map onto the concatenation of lists, it's the
-- same as the concatenation of mapped lists.
-- HINT: do induction on xs
map-++-dist : ∀ {A B : Set} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-dist f xs ys = {!!}
