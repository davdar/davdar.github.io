module Basics-v2 where

infix  4 ∃
infixl 5 _∨_
infixl 6 _∧_
infix  9 ¬_
infix  10 _≡_ _≤ᴺ_ _<ᴺ_
infix  14 _∇?ᴺ_ _∇*ᴺ_ _∇~ᴺ_
infixl 15 _+ᴺ_ _∸ᴺ_ _++ᴸ_
infixl 16 _*ᴺ_
infixl 30 _∘_
infixr 20 _∷_

--------------
-- equality --
--------------

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- ================ --
-- Type Connectives --
-- ================ --

-- empty type --

data 𝟘 : Set where

¬_ : Set → Set
¬ A = A → 𝟘

-- singleton type --

data 𝟙 : Set where
  tt : 𝟙

-- sum type --

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

-- product type --

record _∧_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    projl : A
    projr : B
open _∧_ public

-- dependent sum type --

syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B
record ∃ (A : Set) (B : A → Set) : Set where
  constructor ⟨∃_,_⟩
  field
    dprojl : A
    dprojr : B dprojl
open ∃ public

-- function composition --

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- case analysis --

CASE_OF_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (x : A) (f : A → B) → B
CASE x OF f = f x

-- ============ --
-- TYPE CLASSES --
-- ============ --

-- monoids --

record has[++] (A : Set) : Set where
  infixl 15 _++_
  field
    nil : A
    _++_ : A → A → A
open has[++] {{...}} public

record cor[++] (A : Set) {{_ : has[++] A}} : Set where
  field
    ++-lunit : ∀ (x : A) → nil ++ x ≡ x
    ++-runit : ∀ (x : A) → x ++ nil ≡ x
    ++-assoc : ∀ (x y z : A) → x ++ (y ++ z) ≡ x ++ y ++ z
open cor[++] {{...}} public

-- commutative monoids --

record has[+] (A : Set) : Set where
  infixl 15 _+_
  field
    none : A
    _+_ : A → A → A
open has[+] {{...}} public

record cor[+] (A : Set) {{_ : has[+] A}} : Set where
  field
    +-lunit : ∀ (x : A) → none + x ≡ x
    +-runit : ∀ (x  : A) → x + none ≡ x
    +-assoc : ∀ (x y z : A) → x + (y + z) ≡ x + y + z
    +-commu : ∀ (x y : A) → x + y ≡ y + x
open cor[+] {{...}} public

-- rings --

record has[*] (A : Set) {{_ : has[+] A}} : Set where
  infixl 16 _*_
  field
    one : A
    _*_ : A → A → A
open has[*] {{...}} public

record cor[*] (A : Set) {{_ : has[+] A}} {{_ : cor[+] A}} {{_ : has[*] A}} : Set where
  field
    *-lzero : ∀ (x : A) → none * x ≡ none
    *-rzero : ∀ (x : A) → x * none ≡ none
    *-lunit : ∀ (x : A) → one * x ≡ x
    *-runit : ∀ (x : A) → x * one ≡ x
    *-assoc : ∀ (x y z : A) → x * (y * z) ≡ x * y * z
    *-commu : ∀ (x y : A) → x * y ≡ y * x
    *-ldist : ∀ (x y z : A) → x * (y + z) ≡ x * y + x * z
    *-rdist : ∀ (x y z : A) → (x + y) * z ≡ x * z + y * z
open cor[*] {{...}} public

-- total order --

record has[<] (A : Set) : Set₁ where
  infix 10 _≤_
  infix 10 _<_
  field
    _<_ : A → A → Set
    _≤_ : A → A → Set
open has[<] {{...}} public

record cor[<] (A : Set) {{_ : has[<] A}} : Set₁ where
  field
    ≤-refl : ∀ (x : A) → x ≤ x
    ≤-trans : ∀ (x y z : A) → x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : ∀ (x y : A) → x ≤ y → y ≤ x → x ≡ y
    <-irrefl : ∀ (x : A) → ¬ x < x
    <-trans : ∀ (x y z : A) → x < y → y < z → x < z
    <-trans-l : ∀ (x y z : A) → x ≤ y → y < z → x < z
    <-trans-r : ∀ (x y z : A) → x < y → y ≤ z → x < z
    <-asym : ∀ (x y : A) → ¬ (x < y ∧ y < x)
    <-weaken : ∀ (x y : A) → x < y → x ≤ y
    <-splits : ∀ (x y : A) → x ≤ y → x < y ∨ x ≡ y
open cor[<] {{...}} public

-- comparison --

data Comp[≡] : Set where
  EQ : Comp[≡]
  NE : Comp[≡]

data Comp[≤] : Set where
  LE : Comp[≤]
  GT : Comp[≤]

data Comp[<] : Set where
  LT : Comp[<]
  GE : Comp[<]

data Comp[∇] : Set where
  LT : Comp[∇]
  EQ : Comp[∇]
  GT : Comp[∇]

record has[<?] (A : Set) : Set where
  infix 14 _∇?_ _≤?_ _<?_
  field
    _≡?_ : A → A → Comp[≡]
    _<?_ : A → A → Comp[<]
    _≤?_ : A → A → Comp[≤]
    _∇?_ : A → A → Comp[∇]
open has[<?] {{...}} public

data Ord[≡] {A : Set} (x y : A) : Set where
  EQ : x ≡ y → Ord[≡] x y
  NE : ¬ x ≡ y → Ord[≡] x y

data Link[≡] {A : Set} {x y : A} : Comp[≡] → Ord[≡] x y → Set where
  EQ : ∀ {ε : x ≡ y} → Link[≡] EQ (EQ ε)
  NE : ∀ {ε : ¬ x ≡ y} → Link[≡] NE (NE ε)

data Ord[<][_,_] {A : Set} (_≼_ : A → A → Set) (_≺_ : A → A → Set) (x y : A) : Set where
  LT : x ≺ y → Ord[<][ _≼_ , _≺_ ] x y
  GE : y ≼ x → Ord[<][ _≼_ , _≺_ ] x y

data Link[<][_,_] {A : Set} (_≼_ : A → A → Set) (_≺_ : A → A → Set) {x y : A} : Comp[<] → Ord[<][ _≼_ , _≺_ ] x y → Set where
  LT : ∀ {ε : x ≺ y} → Link[<][ _≼_ , _≺_ ] LT (LT ε)
  GE : ∀ {ε : y ≼ x} → Link[<][ _≼_ , _≺_ ] GE (GE ε)

data Ord[≤][_,_] {A : Set} (_≼_ : A → A → Set) (_≺_ : A → A → Set) (x y : A) : Set where
  LE : x ≼ y → Ord[≤][ _≼_ , _≺_ ] x y
  GT : y ≺ x → Ord[≤][ _≼_ , _≺_ ] x y

data Link[≤][_,_] {A : Set} (_≼_ : A → A → Set) (_≺_ : A → A → Set) {x y : A} : Comp[≤] → Ord[≤][ _≼_ , _≺_ ] x y → Set where
  LE : ∀ {ε : x ≼ y} → Link[≤][ _≼_ , _≺_ ] LE (LE ε)
  GT : ∀ {ε : y ≺ x} → Link[≤][ _≼_ , _≺_ ] GT (GT ε)

data Ord[∇][_] {A : Set} (_≺_ : A → A → Set) (x y : A) : Set where
  LT : x ≺ y → Ord[∇][ _≺_ ] x y
  EQ : x ≡ y → Ord[∇][ _≺_ ] x y
  GT : y ≺ x → Ord[∇][ _≺_ ] x y

data Link[∇][_] {A : Set} (_≺_ : A → A → Set) {x y : A} : Comp[∇] → Ord[∇][ _≺_ ] x y → Set where
  LT : ∀ {ε : x ≺ y} → Link[∇][ _≺_ ] LT (LT ε)
  EQ : ∀ {ε : x ≡ y} → Link[∇][ _≺_ ] EQ (EQ ε)
  GT : ∀ {ε : y ≺ x} → Link[∇][ _≺_ ] GT (GT ε)

record cor[<?] (A : Set) {{_ : has[<] A}} {{_ : has[<?] A}} : Set₁ where
  field
    _≡*_ : ∀ (x y : A) → Ord[≡] x y
    _≡~_ : ∀ (x y : A) → Link[≡] (x ≡? y) (x ≡* y)
    _<*_ : ∀ (x y : A) → Ord[<][ _≤_ , _<_ ] x y
    _<~_ : ∀ (x y : A) → Link[<][ _≤_ , _<_ ] (x <? y) (x <* y)
    _≤*_ : ∀ (x y : A) → Ord[≤][ _≤_ , _<_ ] x y
    _≤~_ : ∀ (x y : A) → Link[≤][ _≤_ , _<_ ] (x ≤? y) (x ≤* y)
    _∇*_ : ∀ (x y : A) → Ord[∇][ _<_ ] x y
    _∇~_ : ∀ (x y : A) → Link[∇][ _<_ ] (x ∇? y) (x ∇* y)
open cor[<?] {{...}} public

-- ===== --
-- bools --
-- ===== --

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

-- =============== --
-- natural numbers --
-- =============== --

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

----------------
-- operations --
----------------

_+ᴺ_ : ℕ → ℕ → ℕ
zero    +ᴺ n  =  n
(suc m) +ᴺ n  =  suc (m +ᴺ n)

_*ᴺ_ : ℕ → ℕ → ℕ
zero *ᴺ n     =  zero
(suc m) *ᴺ n  =  n +ᴺ (m *ᴺ n)

_∸ᴺ_ : ℕ → ℕ → ℕ
m       ∸ᴺ zero     =  m
zero    ∸ᴺ (suc n)  =  zero
(suc m) ∸ᴺ (suc n)  =  m ∸ᴺ n

instance
  has[++][ℕ] : has[++] ℕ
  has[++][ℕ] = record { nil = 0 ; _++_ = _+ᴺ_ }
  has[+][ℕ] : has[+] ℕ
  has[+][ℕ] = record { none = 0 ; _+_ = _+ᴺ_ }
  has[*][ℕ] : has[*] ℕ
  has[*][ℕ] = record { one = 1 ; _*_ = _*ᴺ_}

----------
-- laws --
----------

-- plus --

+ᴺ-lunit : ∀ (m : ℕ) → zero +ᴺ m ≡ m
+ᴺ-lunit m = refl

+ᴺ-runit : ∀ (m : ℕ) → m +ᴺ zero ≡ m
+ᴺ-runit zero = refl
+ᴺ-runit (suc m) rewrite +ᴺ-runit m = refl

+ᴺ-rsuc : ∀ (m n : ℕ) → m +ᴺ suc n ≡ suc (m +ᴺ n)
+ᴺ-rsuc zero n = refl
+ᴺ-rsuc (suc m) n rewrite +ᴺ-rsuc m n = refl

+ᴺ-assoc : ∀ (m n p : ℕ) → m +ᴺ (n +ᴺ p) ≡ m +ᴺ n +ᴺ p
+ᴺ-assoc zero n p = refl
+ᴺ-assoc (suc m) n p rewrite +ᴺ-assoc m n p = refl

+ᴺ-commu : ∀ (m n : ℕ) → m +ᴺ n ≡ n +ᴺ m
+ᴺ-commu zero n rewrite +ᴺ-runit n = refl
+ᴺ-commu (suc m) n rewrite +ᴺ-rsuc n m | +ᴺ-commu m n = refl

instance
  cor[++][ℕ] : cor[++] ℕ
  cor[++][ℕ] = record
    { ++-lunit = +ᴺ-lunit
    ; ++-runit = +ᴺ-runit
    ; ++-assoc = +ᴺ-assoc
    }
  cor[+][ℕ] : cor[+] ℕ
  cor[+][ℕ] = record
    { +-lunit = +ᴺ-lunit
    ; +-runit = +ᴺ-runit
    ; +-assoc = +ᴺ-assoc
    ; +-commu = +ᴺ-commu
    }

-- times --

*ᴺ-lzero : ∀ (m : ℕ) → zero *ᴺ m ≡ zero
*ᴺ-lzero m = refl

*ᴺ-rzero : ∀ (m : ℕ) → m *ᴺ zero ≡ zero
*ᴺ-rzero zero = refl
*ᴺ-rzero (suc m) rewrite *ᴺ-rzero m = refl

*ᴺ-lunit : ∀ (m : ℕ) → one *ᴺ m ≡ m
*ᴺ-lunit m rewrite +ᴺ-runit m = refl

*ᴺ-runit : ∀ (m : ℕ) → m *ᴺ 1 ≡ m
*ᴺ-runit zero = refl
*ᴺ-runit (suc m) rewrite *ᴺ-runit m = refl

*ᴺ-rsuc : ∀ (m n : ℕ) → m *ᴺ suc n ≡ m +ᴺ m *ᴺ n
*ᴺ-rsuc zero n = refl
*ᴺ-rsuc (suc m) n
  rewrite *ᴺ-rsuc m n
        | +ᴺ-assoc n m (m *ᴺ n)
        | +ᴺ-assoc m n (m *ᴺ n)
        | +ᴺ-commu m n 
        = refl

*ᴺ-rdist : ∀ (m n p : ℕ) → (m +ᴺ n) *ᴺ p ≡ (m *ᴺ p) +ᴺ (n *ᴺ p)
*ᴺ-rdist zero n p = refl
*ᴺ-rdist (suc m) n p rewrite *ᴺ-rdist m n p | +ᴺ-assoc p (m *ᴺ p) (n *ᴺ p) = refl

*ᴺ-assoc : ∀ (m n p : ℕ) → m *ᴺ (n *ᴺ p) ≡ m *ᴺ n *ᴺ p
*ᴺ-assoc zero n p = refl
*ᴺ-assoc (suc m) n p rewrite *ᴺ-rdist n (m *ᴺ n) p | *ᴺ-assoc m n p = refl

*ᴺ-commu : ∀ (m n : ℕ) → m *ᴺ n ≡ n *ᴺ m
*ᴺ-commu zero n rewrite *ᴺ-rzero n = refl
*ᴺ-commu (suc m) n rewrite *ᴺ-commu m n | *ᴺ-rsuc n m = refl

*ᴺ-ldist : ∀ (m n p : ℕ) → m *ᴺ (n +ᴺ p) ≡ (m *ᴺ n) +ᴺ (m *ᴺ p)
*ᴺ-ldist m n p rewrite *ᴺ-commu m (n +ᴺ p) | *ᴺ-rdist n p m | *ᴺ-commu n m | *ᴺ-commu m p = refl

instance
  cor[*][ℕ] : cor[*] ℕ
  cor[*][ℕ] = record
    { *-lzero = *ᴺ-lzero
    ; *-rzero = *ᴺ-rzero
    ; *-lunit = *ᴺ-lunit
    ; *-runit = *ᴺ-runit
    ; *-assoc = *ᴺ-assoc
    ; *-commu = *ᴺ-commu
    ; *-ldist = *ᴺ-ldist
    ; *-rdist = *ᴺ-rdist
    }

--------------
-- ordering --
--------------

data _≤ᴺ_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ} → zero ≤ᴺ n
  suc : ∀ {m n : ℕ} → m ≤ᴺ n → suc m ≤ᴺ suc n

data _<ᴺ_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ}
    → zero <ᴺ suc n
  suc : ∀ {m n : ℕ}
    → m <ᴺ n
    → suc m <ᴺ suc n

instance
  has[<][ℕ] : has[<] ℕ
  has[<][ℕ] = record { _<_ = _<ᴺ_ ; _≤_ = _≤ᴺ_ }

≤-to-< : ∀ {m n : ℕ} → m ≤ n → m < suc n
≤-to-< zero = zero
≤-to-< (suc ε) = suc (≤-to-< ε)

<-to-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-to-≤ zero = suc zero
<-to-≤ (suc ε) = suc (<-to-≤ ε)

≤-fr-< : ∀ {m n : ℕ} → m < suc n → m ≤ n
≤-fr-< zero = zero
≤-fr-< (suc ε) = <-to-≤ ε

<-fr-≤ : ∀ {m n : ℕ} → suc m ≤ n → m < n
<-fr-≤ (suc ε) = ≤-to-< ε

≤ᴺ-refl : ∀ (m : ℕ) → m ≤ᴺ m
≤ᴺ-refl zero = zero
≤ᴺ-refl (suc m) = suc (≤ᴺ-refl m)

≤ᴺ-trans : ∀ (m n p : ℕ) → m ≤ᴺ n → n ≤ᴺ p → m ≤ᴺ p
≤ᴺ-trans _ _ _ zero ε₁ = zero
≤ᴺ-trans _ _ _ (suc ε₁) (suc ε₂) = suc (≤ᴺ-trans _ _ _ ε₁ ε₂)

≤ᴺ-antisym : ∀ (m n : ℕ) → m ≤ᴺ n → n ≤ᴺ m → m ≡ n
≤ᴺ-antisym _ _ zero zero = refl
≤ᴺ-antisym _ _ (suc ε₁) (suc ε₂) rewrite ≤ᴺ-antisym _ _ ε₁ ε₂ = refl

<ᴺ-irrefl : ∀ (m : ℕ) → ¬ (m <ᴺ m)
<ᴺ-irrefl zero ()
<ᴺ-irrefl (suc m) (suc ε) = <ᴺ-irrefl m ε

<ᴺ-trans-l : ∀ (m n p : ℕ) → m ≤ᴺ n → n <ᴺ p → m <ᴺ p
<ᴺ-trans-l _ _ _ zero zero = zero
<ᴺ-trans-l _ _ _ zero (suc ε₂) = zero
<ᴺ-trans-l _ _ _ (suc ε₁) (suc ε₂) = suc (<ᴺ-trans-l _ _ _ ε₁ ε₂)

<ᴺ-trans-r : ∀ (m n p : ℕ) → m <ᴺ n → n ≤ᴺ p → m <ᴺ p
<ᴺ-trans-r _ _ _ zero (suc ε₂) = zero
<ᴺ-trans-r _ _ _ (suc ε₁) (suc ε₂) = suc (<ᴺ-trans-r _ _ _ ε₁ ε₂)

<ᴺ-weaken : ∀ (m n : ℕ) → m < n → m ≤ n
<ᴺ-weaken _ _ zero = zero
<ᴺ-weaken _ _ (suc ε) = suc (<ᴺ-weaken _ _ ε)

<ᴺ-trans : ∀ (m n p : ℕ) → m <ᴺ n → n <ᴺ p → m <ᴺ p
<ᴺ-trans _ _ _ ε₁ ε₂ = <ᴺ-trans-l _ _ _ (<ᴺ-weaken _ _ ε₁) ε₂

<ᴺ-asym : ∀ (m n : ℕ) → ¬ (m <ᴺ n ∧ n <ᴺ m)
<ᴺ-asym m n ⟨ ε₁ , ε₂ ⟩ = <ᴺ-irrefl n (<ᴺ-trans _ _ _ ε₂ ε₁)

<ᴺ-splits : ∀ (m n : ℕ) → m ≤ n → m < n ∨ m ≡ n
<ᴺ-splits zero zero zero = inr refl
<ᴺ-splits zero (suc n) zero = inl zero
<ᴺ-splits (suc m) zero ()
<ᴺ-splits (suc m) (suc n) (suc ε) with <ᴺ-splits m n ε
… | inl ε′ = inl (suc ε′)
… | inr ε′ rewrite ε′ = inr refl

instance
  cor[<][ℕ] : cor[<] ℕ
  cor[<][ℕ] = record
    { ≤-refl = ≤ᴺ-refl
    ; ≤-trans = ≤ᴺ-trans
    ; ≤-antisym = ≤ᴺ-antisym
    ; <-irrefl = <ᴺ-irrefl
    ; <-trans = <ᴺ-trans
    ; <-trans-l = <ᴺ-trans-l
    ; <-trans-r = <ᴺ-trans-r
    ; <-asym = <ᴺ-asym
    ; <-weaken = <ᴺ-weaken
    ; <-splits = <ᴺ-splits
    }

<ᴺ-rmono : ∀ (m n p : ℕ) → m < n → m < n + p
<ᴺ-rmono _ _ p zero = zero
<ᴺ-rmono _ _ p (suc ε) = suc (<ᴺ-rmono _ _ p ε)

<ᴺ-lmono : ∀ (m n p : ℕ) → m < p → m < n + p
<ᴺ-lmono m n p ε rewrite +-commu n p = <ᴺ-rmono m p n ε

----------------
-- comparison --
----------------

_≡?ᴺ_ : ℕ → ℕ → Comp[≡]
zero ≡?ᴺ zero = EQ
zero ≡?ᴺ suc y = NE
suc x ≡?ᴺ zero = NE
suc x ≡?ᴺ suc y = x ≡?ᴺ y 

_≡*ᴺ_ : ∀ (x y : ℕ) → Ord[≡] x y
zero ≡*ᴺ zero = EQ refl
zero ≡*ᴺ suc y = NE (λ ())
suc x ≡*ᴺ zero = NE (λ ())
suc x ≡*ᴺ suc y with x ≡*ᴺ y
… | EQ ε rewrite ε = EQ refl
… | NE ε = NE λ where refl → ε refl

_≡~ᴺ_ : ∀ (x y : ℕ) → Link[≡] (x ≡?ᴺ y) (x ≡*ᴺ y)
zero ≡~ᴺ zero = EQ
zero ≡~ᴺ suc y = NE
suc x ≡~ᴺ zero = NE
suc x ≡~ᴺ suc y with x ≡?ᴺ y | x ≡*ᴺ y | x ≡~ᴺ y
… | EQ | EQ ε | EQ rewrite ε = EQ
… | NE | NE ε | NE = NE

_<?ᴺ_ : ℕ → ℕ → Comp[<]
zero <?ᴺ zero = GE
zero <?ᴺ suc n = LT
suc m <?ᴺ zero = GE
suc m <?ᴺ suc n = m <?ᴺ n

_<*ᴺ_ : ∀ (m n : ℕ) → Ord[<][ _≤ᴺ_ , _<ᴺ_ ] m n
zero <*ᴺ zero = GE zero
zero <*ᴺ suc n = LT zero
suc m <*ᴺ zero = GE zero
suc m <*ᴺ suc n with m <*ᴺ n
… | LT ε = LT (suc ε)
… | GE ε = GE (suc ε)

_<~ᴺ_ : ∀ (m n : ℕ) → Link[<][ _≤ᴺ_ , _<ᴺ_ ] (m <?ᴺ n) (m <*ᴺ n)
zero <~ᴺ zero = GE
zero <~ᴺ suc n = LT
suc m <~ᴺ zero = GE
suc m <~ᴺ suc n with m <?ᴺ n | m <*ᴺ n | m <~ᴺ n
… | LT | LT ε | LT = LT
… | GE | GE ε | GE = GE

_≤?ᴺ_ : ℕ → ℕ → Comp[≤]
zero ≤?ᴺ n = LE
suc m ≤?ᴺ zero = GT
suc m ≤?ᴺ suc n = m ≤?ᴺ n

_≤*ᴺ_ : ∀ (m n : ℕ) → Ord[≤][ _≤ᴺ_ , _<ᴺ_ ] m n
zero ≤*ᴺ n = LE zero
suc m ≤*ᴺ zero = GT zero
suc m ≤*ᴺ suc n with m ≤*ᴺ n
… | LE ε = LE (suc ε)
… | GT ε = GT (suc ε)

_≤~ᴺ_ : ∀ (m n : ℕ) → Link[≤][ _≤ᴺ_ , _<ᴺ_ ] (m ≤?ᴺ n) (m ≤*ᴺ n)
zero ≤~ᴺ n = LE
suc m ≤~ᴺ zero = GT
suc m ≤~ᴺ suc n with m ≤?ᴺ n | m ≤*ᴺ n | m ≤~ᴺ n
… | LE | LE ε | LE = LE
… | GT | GT ε | GT = GT

_∇?ᴺ_ : ℕ → ℕ → Comp[∇]
zero ∇?ᴺ zero = EQ
zero ∇?ᴺ suc n = LT
suc m ∇?ᴺ zero = GT
suc m ∇?ᴺ suc n = m ∇?ᴺ n

_∇*ᴺ_ : ∀ (m n : ℕ) → Ord[∇][ _<ᴺ_ ] m n
zero ∇*ᴺ zero = EQ refl
zero ∇*ᴺ suc n = LT zero
suc m ∇*ᴺ zero = GT zero
suc m ∇*ᴺ suc n with m ∇*ᴺ n
… | LT ε = LT (suc ε)
… | EQ ε rewrite ε = EQ refl
… | GT ε = GT (suc ε)

_∇~ᴺ_ : ∀ (m n : ℕ) → Link[∇][ _<ᴺ_ ] (m ∇?ᴺ n) (m ∇*ᴺ n)
zero ∇~ᴺ zero = EQ
zero ∇~ᴺ suc n = LT
suc m ∇~ᴺ zero = GT
suc m ∇~ᴺ suc n with m ∇?ᴺ n | m ∇*ᴺ n | m ∇~ᴺ n
… | LT | LT ε | LT = LT
… | EQ | EQ ε | EQ rewrite ε = EQ
… | GT | GT ε | GT = GT

instance
  has[<?][ℕ] : has[<?] ℕ
  has[<?][ℕ] = record { _≡?_ = _≡?ᴺ_ ; _<?_ = _<?ᴺ_ ; _≤?_ = _≤?ᴺ_ ; _∇?_ = _∇?ᴺ_}
  cor[<?][ℕ] : cor[<?] ℕ
  cor[<?][ℕ] = record
    { _≡*_ = _≡*ᴺ_
    ; _≡~_ = _≡~ᴺ_
    ; _<*_ = _<*ᴺ_
    ; _<~_ = _<~ᴺ_
    ; _≤*_ = _≤*ᴺ_
    ; _≤~_ = _≤~ᴺ_
    ; _∇*_ = _∇*ᴺ_
    ; _∇~_ = _∇~ᴺ_
    }

-- ===== --
-- lists --
-- ===== --

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

------------
-- monoid --
------------

_++ᴸ_ : ∀ {A : Set} → List A → List A → List A
[] ++ᴸ ys = ys
(x ∷ xs) ++ᴸ ys = x ∷ (xs ++ᴸ ys)

instance
  has[++][List] : ∀ {A : Set} → has[++] (List A)
  has[++][List] = record { nil = [] ; _++_ = _++ᴸ_ }

++ᴸ-lunit : ∀ {A : Set} (xs : List A) → [] ++ᴸ xs ≡ xs
++ᴸ-lunit xs = refl

++ᴸ-runit : ∀ {A : Set} (xs : List A) → xs ++ᴸ [] ≡ xs
++ᴸ-runit [] = refl
++ᴸ-runit (x ∷ xs) rewrite ++ᴸ-runit xs = refl

++ᴸ-assoc : ∀ {A : Set} (xs ys zs : List A) → xs ++ᴸ (ys ++ᴸ zs) ≡ xs ++ᴸ ys ++ᴸ zs
++ᴸ-assoc [] ys zs = refl
++ᴸ-assoc (x ∷ xs) ys zs rewrite ++ᴸ-assoc xs ys zs = refl

instance
  cor[++][List] : ∀ {A : Set} → cor[++] (List A)
  cor[++][List] = record { ++-lunit = ++ᴸ-lunit ; ++-runit = ++ᴸ-runit ; ++-assoc = ++ᴸ-assoc }

----------------------
-- other operations --
----------------------

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr f i [] = i
foldr f i (x ∷ xs) = f x (foldr f i xs)

foldl : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldl f i [] = i
foldl f i (x ∷ xs) = foldl f (f x i) xs

-- ====== --
-- Option --
-- ====== --

data Option (A : Set) : Set where
  None : Option A
  Some : A → Option A
  
