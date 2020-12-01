-- [Nearly all of this material is borrowed from [plfa.Connectives]
-- authored by Wen Kokke and Philip Wadler.]
-- 
-- [plfa.Connectives]: https://plfa.github.io/Connectives/

module la7 where

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

-- We've seen some algebraic laws for simple arithmetic:
--
-- 0 + m ≡ m
-- m + n ≡ n + m
-- (m + n) + p ≡ m + (n + p)
--
-- 1 * m ≡ m
-- 0 * m ≡ 0
-- m * n ≡ n * m
-- (m * n) * p ≡ m * (n * p)
-- m * (n + p) ≡ (m * n) + (m * p)
--
-- m ^ 0 ≡ 1
-- m ^ 1 ≡ m
-- (m ^ n) ^ p ≡ m ^ (n * p)
-- m ^ (n + p) ≡ (m ^ n) * (m ^ p)
-- (m * n) ^ p ≡ (m ^ p) * (n ^ p)
--
-- In logic and programming there is a parallel world where:
-- Numbers | Programming | Logic
-- --------|-------------|-------
-- ℕ       | Type        | Prop
-- 0       | {}          | ⊥
-- 1       | {•}         | ⊤
-- +       | ⊎           | ∨
-- *       | ×           | ∧
-- ^       | →           | ⇒
-- ≡       | ≈           | ⇔
--
-- In Agda we fuse Programming and Logic into one universe: Set
--
-- An isomorphism (A ≈ B) is a mapping in each direction:
--
--   to : A → B
--   fr : B → A
--
-- such that round trips are noops:
--
--    ∀ x : A, fr (to x) ≡ x
--    ∀ y : B, to (fr y) ≡ y

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

η-× : ∀ {A B : Set} (xy : A × B) → ⟨ proj₁ xy , proj₂ xy ⟩ ≡ xy
η-× ⟨ x , y ⟩ = refl

-- ×-comm : A × B ≈ B × A

×-comm-L : ∀ {A B : Set} → A × B → B × A
×-comm-L ⟨ x , y ⟩ = ⟨ y , x ⟩

×-comm-R : ∀ {A B : Set} → B × A → A × B
×-comm-R = ×-comm-L

×-comm-iso-L : ∀ {A B : Set} (xy : A × B) → ×-comm-R (×-comm-L xy) ≡ xy
×-comm-iso-L ⟨ x , y ⟩ = refl

×-comm-iso-R : ∀ {A B : Set} (xy : B × A) → ×-comm-L (×-comm-R xy) ≡ xy
×-comm-iso-R xy = ×-comm-iso-L xy

-- ×-assoc : (A × B) × C ≈ A × (B × C)

×-assoc-L : ∀ {A B C : Set} → (A × B) × C → A × (B × C)
×-assoc-L ⟨ ⟨ x , y ⟩ , z ⟩ = ⟨ x , ⟨ y , z ⟩ ⟩

×-assoc-R : ∀ {A B C : Set} → A × (B × C) → (A × B) × C
×-assoc-R ⟨ x , ⟨ y , z ⟩ ⟩ = ⟨ ⟨ x , y ⟩ , z ⟩

×-assoc-iso-L : ∀ {A B C  : Set} (xyz : (A × B) × C) → ×-assoc-R (×-assoc-L xyz) ≡ xyz
×-assoc-iso-L ⟨ ⟨ x , y ⟩ , z ⟩ = refl

×-assoc-iso-R : ∀ {A B C  : Set} (xyz : A × (B × C)) → ×-assoc-L (×-assoc-R xyz) ≡ xyz
×-assoc-iso-R ⟨ x , ⟨ y , z ⟩ ⟩ = refl

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (x : ⊤) → x ≡ tt
η-⊤ tt = refl

-- ⊤-lunit : ⊤ × A ≈ A

⊤-lunit-L : ∀ {A : Set} → ⊤ × A → A
⊤-lunit-L ⟨ tt , x ⟩ = x

⊤-lunit-R : ∀ {A : Set} → A → ⊤ × A 
⊤-lunit-R x = ⟨ tt , x ⟩

⊤-lunit-iso-L : ∀ {A : Set} (xy : ⊤ × A) → ⊤-lunit-R (⊤-lunit-L xy) ≡ xy
⊤-lunit-iso-L ⟨ tt , x ⟩ = refl

⊤-lunit-iso-R : ∀ {A : Set} (x : A) → ⊤-lunit-L (⊤-lunit-R x) ≡ x
⊤-lunit-iso-R x = refl

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

case : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case f g (inj₁ x) = f x
case f g (inj₂ y) = g y

η-⊎ : ∀ {A B C : Set} (xy : A ⊎ B) → case inj₁ inj₂ xy ≡ xy
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

-- ⊎-comm : A ⊎ B ≈ B ⊎ A

⊎-comm-L : ∀ {A B : Set} → A ⊎ B → B ⊎ A
⊎-comm-L (inj₁ x) = inj₂ x
⊎-comm-L (inj₂ y) = inj₁ y

⊎-comm-R : ∀ {A B : Set} → B ⊎ A → A ⊎ B
⊎-comm-R = ⊎-comm-L

⊎-comm-iso-L : ∀ {A B : Set} (xy : A ⊎ B) → ⊎-comm-R (⊎-comm-L xy) ≡ xy
⊎-comm-iso-L (inj₁ x) = refl
⊎-comm-iso-L (inj₂ y) = refl

⊎-comm-iso-R : ∀ {A B : Set} (xy : B ⊎ A) → ⊎-comm-L (⊎-comm-R xy) ≡ xy
⊎-comm-iso-R xy = ⊎-comm-iso-L xy

-- ⊎-assoc : (A ⊎ B) ⊎ C ≈ A ⊎ (B ⊎ C)

⊎-assoc-L : ∀ {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc-L (inj₁ (inj₁ x)) = inj₁ x
⊎-assoc-L (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
⊎-assoc-L (inj₂ z) = inj₂ (inj₂ z)

⊎-assoc-R : ∀ {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
⊎-assoc-R (inj₁ x) = inj₁ (inj₁ x)
⊎-assoc-R (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
⊎-assoc-R (inj₂ (inj₂ z)) = inj₂ z

⊎-assoc-iso-L : ∀ {A B C  : Set} (xyz : (A ⊎ B) ⊎ C) → ⊎-assoc-R (⊎-assoc-L xyz) ≡ xyz
⊎-assoc-iso-L (inj₁ (inj₁ x)) = refl
⊎-assoc-iso-L (inj₁ (inj₂ y)) = refl
⊎-assoc-iso-L (inj₂ z) = refl

⊎-assoc-iso-R : ∀ {A B C : Set} (xyz : A ⊎ (B ⊎ C)) → ⊎-assoc-L (⊎-assoc-R xyz) ≡ xyz
⊎-assoc-iso-R (inj₁ x) = refl
⊎-assoc-iso-R (inj₂ (inj₁ y)) = refl
⊎-assoc-iso-R (inj₂ (inj₂ z)) = refl

-- ⊎-rdist : (A ⊎ B) × C ≈ (A × C) ⊎ (B × C)

⊎-rdist-L : ∀ {A B C : Set} → (A ⊎ B) × C → (A × C) ⊎ (B × C)
⊎-rdist-L ⟨ inj₁ x , z ⟩ = inj₁ ⟨ x , z ⟩
⊎-rdist-L ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩

⊎-rdist-R : ∀ {A B C : Set} → (A × C) ⊎ (B × C) → (A ⊎ B) × C 
⊎-rdist-R (inj₁ ⟨ x , z ⟩) = ⟨ inj₁ x , z ⟩
⊎-rdist-R (inj₂ ⟨ y , z ⟩) = ⟨ inj₂ y , z ⟩

⊎-rdist-iso-L : ∀ {A B C : Set} (xyz : (A ⊎ B) × C) → ⊎-rdist-R (⊎-rdist-L xyz) ≡ xyz
⊎-rdist-iso-L ⟨ inj₁ x , z ⟩ = refl
⊎-rdist-iso-L ⟨ inj₂ y , z ⟩ = refl

⊎-rdist-iso-R : ∀ {A B C : Set} (xzyz : (A × C) ⊎ (B × C) ) → ⊎-rdist-L (⊎-rdist-R xzyz) ≡ xzyz
⊎-rdist-iso-R (inj₁ ⟨ x , z ⟩) = refl
⊎-rdist-iso-R (inj₂ ⟨ y , z ⟩) = refl

-- Q: what about:
--
-- ×-rdist : (A × B) ⊎ C ≈ (A ⊎ C) × (B ⊎ C)

×-rdist-L : ∀ {A B C : Set} → (A × B) ⊎ C → (A ⊎ C) × (B ⊎ C)
×-rdist-L (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
×-rdist-L (inj₂ z) = ⟨ inj₂ z , inj₂ z ⟩

×-rdist-R : ∀ {A B C : Set} → (A ⊎ C) × (B ⊎ C) → (A × B) ⊎ C
×-rdist-R ⟨ inj₁ x , inj₁ y ⟩   = inj₁ ⟨ x , y ⟩
×-rdist-R ⟨ inj₁ x , inj₂ z ⟩   = inj₂ z
×-rdist-R ⟨ inj₂ z , inj₁ y ⟩   = inj₂ z
×-rdist-R ⟨ inj₂ z₁ , inj₂ z₂ ⟩ = inj₂ z₁

×-rdist-iso-L : ∀ {A B C : Set} (xyz : (A × B) ⊎ C) → ×-rdist-R (×-rdist-L xyz) ≡ xyz
×-rdist-iso-L (inj₁ ⟨ x , y ⟩) = refl
×-rdist-iso-L (inj₂ z) = refl

×-rdist-iso-R : ∀ {A B C : Set} (xzyz : (A ⊎ C) × (B ⊎ C)) → ×-rdist-L (×-rdist-R xzyz) ≡ xzyz
×-rdist-iso-R ⟨ inj₁ x , inj₁ y ⟩ = refl
×-rdist-iso-R ⟨ inj₁ x , inj₂ z ⟩ = {!!} -- NOT PROVABLE
×-rdist-iso-R ⟨ inj₂ z , inj₁ x ⟩ = {!!} -- NOT PROVABLE
×-rdist-iso-R ⟨ inj₂ z₁ , inj₂ z₂ ⟩ = {!!} -- NOT PROVABLE

data ⊥ : Set where
  -- no clauses!

exfalso : ∀ {A : Set} → ⊥ → A
exfalso ()

η-⊥ : ∀ {A : Set} (f : ⊥ → A) (x : ⊥) → f x ≡ exfalso x
η-⊥ f ()

-- ⊥-lunit : ⊥ ⊎ A ≈ A

⊥-lunit-L : ∀ {A : Set} → ⊥ ⊎ A → A
⊥-lunit-L (inj₁ ())
⊥-lunit-L (inj₂ x) = x

⊥-lunit-R : ∀ {A : Set} → A → ⊥ ⊎ A
⊥-lunit-R x = inj₂ x

⊥-lunit-iso-L : ∀ {A : Set} (xy : ⊥ ⊎ A) → ⊥-lunit-R (⊥-lunit-L xy) ≡ xy
⊥-lunit-iso-L (inj₁ ())
⊥-lunit-iso-L (inj₂ x) = refl

⊥-lunit-iso-R : ∀ {A : Set} (x : A) → ⊥-lunit-L (⊥-lunit-R x) ≡ x
⊥-lunit-iso-R x = refl

-- ⊥-lzero : ⊥ × A ≈ ⊥

⊥-lzero-L : ∀ {A : Set} → ⊥ × A → ⊥
⊥-lzero-L ⟨ () , x ⟩

⊥-lzero-R : ∀ {A : Set} → ⊥ → ⊥ × A
⊥-lzero-R ()

⊥-lzero-iso-L : ∀ {A : Set} (xy : ⊥ × A) → ⊥-lzero-R (⊥-lzero-L xy) ≡ xy
⊥-lzero-iso-L ⟨ () , x ⟩

⊥-lzero-iso-R : ∀ {A : Set} (x : ⊥) → ⊥-lzero-L {A = A} (⊥-lzero-R x) ≡ x
⊥-lzero-iso-R ()

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
