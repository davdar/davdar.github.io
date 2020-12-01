module ic7 where

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
η-× xy = {!!}

-- ×-comm : A × B ≈ B × A

×-comm-L : ∀ {A B : Set} → A × B → B × A
×-comm-L xy = {!!}

×-comm-R : ∀ {A B : Set} → B × A → A × B
×-comm-R = ×-comm-L

×-comm-iso-L : ∀ {A B : Set} (xy : A × B) → ×-comm-R (×-comm-L xy) ≡ xy
×-comm-iso-L xy = {!!}

×-comm-iso-R : ∀ {A B : Set} (xy : B × A) → ×-comm-L (×-comm-R xy) ≡ xy
×-comm-iso-R xy = ×-comm-iso-L xy

-- ×-assoc : (A × B) × C ≈ A × (B × C)

×-assoc-L : ∀ {A B C : Set} → (A × B) × C → A × (B × C)
×-assoc-L xyz = {!!}

×-assoc-R : ∀ {A B C : Set} → A × (B × C) → (A × B) × C
×-assoc-R xyz = {!!}

×-assoc-iso-L : ∀ {A B C  : Set} (xyz : (A × B) × C) → ×-assoc-R (×-assoc-L xyz) ≡ xyz
×-assoc-iso-L xyz = {!!}

×-assoc-iso-R : ∀ {A B C  : Set} (xyz : A × (B × C)) → ×-assoc-L (×-assoc-R xyz) ≡ xyz
×-assoc-iso-R xyz = {!!}

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (x : ⊤) → x ≡ tt
η-⊤ t = {!!}

-- ⊤-lunit : ⊤ × A ≈ A

⊤-lunit-L : ∀ {A : Set} → ⊤ × A → A
⊤-lunit-L tx = {!!}

⊤-lunit-R : ∀ {A : Set} → A → ⊤ × A 
⊤-lunit-R x = {!!}

⊤-lunit-iso-L : ∀ {A : Set} (xy : ⊤ × A) → ⊤-lunit-R (⊤-lunit-L xy) ≡ xy
⊤-lunit-iso-L tx = {!!}

⊤-lunit-iso-R : ∀ {A : Set} (x : A) → ⊤-lunit-L (⊤-lunit-R x) ≡ x
⊤-lunit-iso-R x = {!!}

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
η-⊎ xy = {!!}

-- ⊎-comm : A ⊎ B ≈ B ⊎ A

⊎-comm-L : ∀ {A B : Set} → A ⊎ B → B ⊎ A
⊎-comm-L xy = {!!}

⊎-comm-R : ∀ {A B : Set} → B ⊎ A → A ⊎ B
⊎-comm-R = ⊎-comm-L

⊎-comm-iso-L : ∀ {A B : Set} (xy : A ⊎ B) → ⊎-comm-R (⊎-comm-L xy) ≡ xy
⊎-comm-iso-L xy = {!!}

⊎-comm-iso-R : ∀ {A B : Set} (xy : B ⊎ A) → ⊎-comm-L (⊎-comm-R xy) ≡ xy
⊎-comm-iso-R xy = ⊎-comm-iso-L xy

-- ⊎-assoc : (A ⊎ B) ⊎ C ≈ A ⊎ (B ⊎ C)

⊎-assoc-L : ∀ {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc-L xyz = {!!}

⊎-assoc-R : ∀ {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
⊎-assoc-R xyz = {!!}

⊎-assoc-iso-L : ∀ {A B C  : Set} (xyz : (A ⊎ B) ⊎ C) → ⊎-assoc-R (⊎-assoc-L xyz) ≡ xyz
⊎-assoc-iso-L xyz = {!!}

⊎-assoc-iso-R : ∀ {A B C : Set} (xyz : A ⊎ (B ⊎ C)) → ⊎-assoc-L (⊎-assoc-R xyz) ≡ xyz
⊎-assoc-iso-R xyz = {!!}

-- ⊎-rdist : (A ⊎ B) × C ≈ (A × C) ⊎ (B × C)

⊎-rdist-L : ∀ {A B C : Set} → (A ⊎ B) × C → (A × C) ⊎ (B × C)
⊎-rdist-L xyz = {!!}

⊎-rdist-R : ∀ {A B C : Set} → (A × C) ⊎ (B × C) → (A ⊎ B) × C 
⊎-rdist-R xyz = {!!}

⊎-rdist-iso-L : ∀ {A B C : Set} (xyz : (A ⊎ B) × C) → ⊎-rdist-R (⊎-rdist-L xyz) ≡ xyz
⊎-rdist-iso-L xyz = {!!}

⊎-rdist-iso-R : ∀ {A B C : Set} (xzyz : (A × C) ⊎ (B × C) ) → ⊎-rdist-L (⊎-rdist-R xzyz) ≡ xzyz
⊎-rdist-iso-R xyz = {!!}

-- Q: what about:
--
-- ×-rdist : (A × B) ⊎ C ≈ (A ⊎ C) × (B ⊎ C)

×-rdist-L : ∀ {A B C : Set} → (A × B) ⊎ C → (A ⊎ C) × (B ⊎ C)
×-rdist-L xyz = {!!}

×-rdist-R : ∀ {A B C : Set} → (A ⊎ C) × (B ⊎ C) → (A × B) ⊎ C
×-rdist-R xzyz = {!!}

×-rdist-iso-L : ∀ {A B C : Set} (xyz : (A × B) ⊎ C) → ×-rdist-R (×-rdist-L xyz) ≡ xyz
×-rdist-iso-L xy = {!!}

×-rdist-iso-R : ∀ {A B C : Set} (xzyz : (A ⊎ C) × (B ⊎ C)) → ×-rdist-L (×-rdist-R xzyz) ≡ xzyz
×-rdist-iso-R xzyz = {!!}

data ⊥ : Set where
  -- no clauses!

exfalso : ∀ {A : Set} → ⊥ → A
exfalso b = {!!}

η-⊥ : ∀ {A : Set} (f : ⊥ → A) (x : ⊥) → f x ≡ exfalso x
η-⊥ f b = {!!}

-- ⊥-lunit : ⊥ ⊎ A ≈ A

⊥-lunit-L : ∀ {A : Set} → ⊥ ⊎ A → A
⊥-lunit-L bx = {!!}

⊥-lunit-R : ∀ {A : Set} → A → ⊥ ⊎ A
⊥-lunit-R x = {!!}

⊥-lunit-iso-L : ∀ {A : Set} (xy : ⊥ ⊎ A) → ⊥-lunit-R (⊥-lunit-L xy) ≡ xy
⊥-lunit-iso-L bx = {!!}

⊥-lunit-iso-R : ∀ {A : Set} (x : A) → ⊥-lunit-L (⊥-lunit-R x) ≡ x
⊥-lunit-iso-R x = {!!}

-- ⊥-lzero : ⊥ × A ≈ ⊥

⊥-lzero-L : ∀ {A : Set} → ⊥ × A → ⊥
⊥-lzero-L bx = {!!}

⊥-lzero-R : ∀ {A : Set} → ⊥ → ⊥ × A
⊥-lzero-R b = {!!}

⊥-lzero-iso-L : ∀ {A : Set} (xy : ⊥ × A) → ⊥-lzero-R (⊥-lzero-L xy) ≡ xy
⊥-lzero-iso-L bx = {!!}

⊥-lzero-iso-R : ∀ {A : Set} (x : ⊥) → ⊥-lzero-L {A = A} (⊥-lzero-R x) ≡ x
⊥-lzero-iso-R b = {!!}

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
fun-ldist-R fg yz = {!!}

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
fun-rdist-R fg z = {!!}

fun-rdist-L-iso-ext : ∀ {A B C : Set} (f : (A × B) ^^ C) (z : C) → fun-rdist-R (fun-rdist-L f) z ≡ f z
fun-rdist-L-iso-ext f z = {!!}

fun-rdist-R-iso : ∀ {A B C : Set} (fg : (A ^^ C) × (B ^^ C)) → fun-rdist-L (fun-rdist-R fg) ≡ fg
fun-rdist-R-iso fg = {!!}
