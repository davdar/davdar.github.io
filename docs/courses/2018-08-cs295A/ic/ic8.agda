module ic8 where

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

--------------
-- IN CLASS --
--------------

-- exponentiation is the function space flipped
-- A ^^ B ≜ B → A

_^^_ : Set → Set → Set
A ^^ B = B → A

η-fun : ∀ {A B : Set} (f : A ^^ B) → (λ (x : B) → f x) ≡ f
η-fun f = {!!}

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

-- fun-curry : (A ^^ B) ^^ C ≈ A ^^ (C × B)
-- fun-curry : C → (B → A) ≈ (C × B) → A

fun-curry-L : ∀ {A B C : Set} → (A ^^ B) ^^ C → A ^^ (B × C)
fun-curry-L f yz = {!!}

fun-curry-R : ∀ {A B C : Set} → A ^^ (B × C) → (A ^^ B) ^^ C
fun-curry-R f z y = {!!}

fun-curry-iso-L : ∀ {A B C : Set} (f : (A ^^ B) ^^ C) → fun-curry-R (fun-curry-L f) ≡ f
fun-curry-iso-L f = {!!}

fun-curry-iso-R-ext : ∀ {A B C : Set} (f : A ^^ (B × C)) (yz : B × C) → fun-curry-L (fun-curry-R f) yz ≡ f yz
fun-curry-iso-R-ext f yz = {!!}

fun-curry-iso-R : ∀ {A B C : Set} (f : A ^^ (B × C)) → fun-curry-L (fun-curry-R f) ≡ f
fun-curry-iso-R f = {!!}

-- fun-ldist : A ^^ (B ⊎ C) ≈ (A ^^ B) × (A ^^ C)
-- fun-ldist : B ⊎ C → A ≈ (B → A) × (C → A)

fun-ldist-L : ∀ {A B C : Set} → A ^^ (B ⊎ C) → A ^^ B × A ^^ C
fun-ldist-L f = {!!}

fun-ldist-R : ∀ {A B C : Set} → A ^^ B × A ^^ C → A ^^ (B ⊎ C)
fun-ldist-R fg = {!!}

fun-ldist-iso-L-ext : ∀ {A B C : Set} (f : A ^^ (B ⊎ C)) (yz : B ⊎ C) → fun-ldist-R (fun-ldist-L f) yz ≡ f yz
fun-ldist-iso-L-ext f yz = {!!}

fun-ldist-iso-L : ∀ {A B C : Set} (f : A ^^ (B ⊎ C)) → fun-ldist-R (fun-ldist-L f) ≡ f
fun-ldist-iso-L f = {!!}

fun-ldist-iso-R : ∀ {A B C : Set} (f : A ^^ B × A ^^ C) → fun-ldist-L (fun-ldist-R f) ≡ f
fun-ldist-iso-R fg = {!!}

-- fun-rdist : (A × B) ^^ C ≈ (A ^^ C) × (B ^^ C)
-- fun-rdist : C → (A × B) ≈ (C → A) × (C → B)

fun-rdist-L : ∀ {A B C : Set} → (A × B) ^^ C → (A ^^ C) × (B ^^ C)
fun-rdist-L f = {!!}

fun-rdist-R : ∀ {A B C : Set} → (A ^^ C) × (B ^^ C) → (A × B) ^^ C 
fun-rdist-R fg = {!!}

fun-rdist-L-iso-ext : ∀ {A B C : Set} (f : (A × B) ^^ C) (z : C) → fun-rdist-R (fun-rdist-L f) z ≡ f z
fun-rdist-L-iso-ext f z = {!!}

fun-rdist-R-iso : ∀ {A B C : Set} (fg : (A ^^ C) × (B ^^ C)) → fun-rdist-L (fun-rdist-R fg) ≡ fg
fun-rdist-R-iso fg = {!!}

infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = {!!}

¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬-elim ¬¬¬x = {!!}

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y = {!!}

_≢_ : ∀ {A : Set} (x y : A) → Set
x ≢ y = {!!}

e1 : 1 ≢ 2
e1 = {!!}

_ : 1 ≢ 2
_ = {!!}

postulate
  excluded-middle : ∀ {A : Set} → A ⊎ ¬ A

¬¬excluded-middle : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
¬¬excluded-middle P = {!!}

+-lsuc : ∀ (m n : ℕ) → suc m + n ≡ suc (m + n)
+-lsuc = {!!}

infix 2 ∃
syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B
data ∃ (A : Set) (B : A → Set) : Set where
  ⟨∃_,_⟩ : (x : A) → B x → ∃ A B

mutual
  data even : ℕ → Set where
    zero : even zero
    suc : ∀ {m : ℕ}
      → odd m
      → even (suc m)
  data odd : ℕ → Set where
    suc : ∀ {m : ℕ}
      → even m
      → odd (suc m)

mutual
  even-∃ : ∀ {m : ℕ} → even m → ∃[ n ∈ ℕ ] n * 2 ≡ m
  even-∃ e[m] = {!!}
  
  odd-∃ : ∀ {m : ℕ} → odd m → ∃[ n ∈ ℕ ] n * 2 ≡ suc m
  odd-∃ o[m] = {!!}
