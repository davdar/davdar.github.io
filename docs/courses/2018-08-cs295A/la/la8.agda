-- [Nearly all of this material is borrowed from [plfa.Negation]
-- authored by Wen Kokke and Philip Wadler.]
-- 
-- [plfa.Negation]: https://plfa.github.io/Quantifiers/

module la8 where

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
η-fun f = refl

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

-- fun-curry : (A ^^ B) ^^ C ≈ A ^^ (C × B)
-- fun-curry : C → (B → A) ≈ (C × B) → A

fun-curry-L : ∀ {A B C : Set} → (A ^^ B) ^^ C → A ^^ (B × C)
fun-curry-L f ⟨ y , z ⟩ = f z y

fun-curry-R : ∀ {A B C : Set} → A ^^ (B × C) → (A ^^ B) ^^ C
fun-curry-R f z y = f ⟨ y , z ⟩

fun-curry-iso-L : ∀ {A B C : Set} (f : (A ^^ B) ^^ C) → fun-curry-R (fun-curry-L f) ≡ f
fun-curry-iso-L f = refl

fun-curry-iso-R-ext : ∀ {A B C : Set} (f : A ^^ (B × C)) (yz : B × C) → fun-curry-L (fun-curry-R f) yz ≡ f yz
fun-curry-iso-R-ext f ⟨ y , z ⟩ = refl

fun-curry-iso-R : ∀ {A B C : Set} (f : A ^^ (B × C)) → fun-curry-L (fun-curry-R f) ≡ f
fun-curry-iso-R f = extensionality (fun-curry-iso-R-ext f)

-- fun-ldist : A ^^ (B ⊎ C) ≈ (A ^^ B) × (A ^^ C)
-- fun-ldist : B ⊎ C → A ≈ (B → A) × (C → A)

fun-ldist-L : ∀ {A B C : Set} → A ^^ (B ⊎ C) → A ^^ B × A ^^ C
fun-ldist-L f = ⟨ (λ y → f (inj₁ y)) , (λ z → f (inj₂ z)) ⟩

fun-ldist-R : ∀ {A B C : Set} → A ^^ B × A ^^ C → A ^^ (B ⊎ C)
fun-ldist-R ⟨ f , g ⟩ (inj₁ y) = f y
fun-ldist-R ⟨ f , g ⟩ (inj₂ z) = g z

fun-ldist-iso-L-ext : ∀ {A B C : Set} (f : A ^^ (B ⊎ C)) (yz : B ⊎ C) → fun-ldist-R (fun-ldist-L f) yz ≡ f yz
fun-ldist-iso-L-ext f (inj₁ y) = refl
fun-ldist-iso-L-ext f (inj₂ z) = refl

fun-ldist-iso-L : ∀ {A B C : Set} (f : A ^^ (B ⊎ C)) → fun-ldist-R (fun-ldist-L f) ≡ f
fun-ldist-iso-L f = extensionality (fun-ldist-iso-L-ext f)

fun-ldist-iso-R : ∀ {A B C : Set} (f : A ^^ B × A ^^ C) → fun-ldist-L (fun-ldist-R f) ≡ f
fun-ldist-iso-R ⟨ f , g ⟩ = refl

-- fun-rdist : (A × B) ^^ C ≈ (A ^^ C) × (B ^^ C)
-- fun-rdist : C → (A × B) ≈ (C → A) × (C → B)

fun-rdist-L : ∀ {A B C : Set} → (A × B) ^^ C → (A ^^ C) × (B ^^ C)
fun-rdist-L f = ⟨ (λ z → proj₁ (f z)) , (λ z → proj₂ (f z)) ⟩

fun-rdist-R : ∀ {A B C : Set} → (A ^^ C) × (B ^^ C) → (A × B) ^^ C 
fun-rdist-R ⟨ f , g ⟩ z = ⟨ f z , g z ⟩

fun-rdist-L-iso-ext : ∀ {A B C : Set} (f : (A × B) ^^ C) (z : C) → fun-rdist-R (fun-rdist-L f) z ≡ f z
fun-rdist-L-iso-ext f z with f z
… | ⟨ x , y ⟩ = refl

fun-rdist-R-iso : ∀ {A B C : Set} (fg : (A ^^ C) × (B ^^ C)) → fun-rdist-L (fun-rdist-R fg) ≡ fg
fun-rdist-R-iso ⟨ f , g ⟩ = refl

-- Negation

infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

-- in classical logic, A ≈ ¬ ¬ A
-- computationally, this isomorphism does not hold. However, it holds
-- *underneath negation*

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x

¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬-elim ¬¬¬x = λ x → ¬¬¬x (λ ¬x → ¬x x)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y = λ x → ¬y (f x)

_≢_ : ∀ {A : Set} (x y : A) → Set
x ≢ y = ¬ (x ≡ y)

e1 : 1 ≢ 2
e1 ()

_ : 1 ≢ 2
_ = λ ()

-- excluded middle is not provable

postulate
  excluded-middle : ∀ {A : Set} → A ⊎ ¬ A

¬¬excluded-middle : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
¬¬excluded-middle P = P (inj₂ (λ x → P (inj₁ x)))

+-lsuc : ∀ (m n : ℕ) → suc m + n ≡ suc (m + n)
+-lsuc = λ m n → refl

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
  even-∃ zero = ⟨∃ zero , refl ⟩
  even-∃ (suc o[m]) = odd-∃ o[m]
  
  odd-∃ : ∀ {m : ℕ} → odd m → ∃[ n ∈ ℕ ] n * 2 ≡ suc m
  odd-∃ (suc e[m]) with even-∃ e[m]
  … | ⟨∃ n , P[n] ⟩ rewrite sym P[n] = ⟨∃ suc n , refl ⟩
