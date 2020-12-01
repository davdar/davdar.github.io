module Basics-v-consolidated where

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

absurd : ∀ {A : Set} → 𝟘 → A
absurd ()

-- singleton type --

data 𝟙 : Set where
  TT : 𝟙

-- sum type --

data _∨_ (A B : Set) : Set where
  Inl : A → A ∨ B
  Inr : B → A ∨ B

-- product type --

record _∧_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B
open _∧_ public

-- dependent sum type --

syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B
record ∃ (A : Set) (B : A → Set) : Set where
  constructor ⟨∃_,_⟩
  field
    dfst : A
    dsnd : B dfst
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
    null : A
    _++_ : A → A → A
open has[++] {{...}} public

{-# DISPLAY has[++].null _ = null #-}
{-# DISPLAY has[++]._++_ _ = _++_ #-}

record cor[++] (A : Set) {{_ : has[++] A}} : Set where
  field
    ++-lunit : ∀ (x : A) → null ++ x ≡ x
    ++-runit : ∀ (x : A) → x ++ null ≡ x
    ++-assoc : ∀ (x y z : A) → x ++ (y ++ z) ≡ x ++ y ++ z
open cor[++] {{...}} public

{-# DISPLAY cor[++].++-lunit _ = ++-lunit #-}
{-# DISPLAY cor[++].++-runit _ = ++-runit #-}
{-# DISPLAY cor[++].++-assoc _ = ++-assoc #-}

-- commutative monoids --

record has[+] (A : Set) : Set where
  infixl 15 _+_
  field
    zero : A
    _+_ : A → A → A
open has[+] {{...}} public

{-# DISPLAY has[+].zero _ = zero #-}
{-# DISPLAY has[+]._+_ _ = _+_ #-}

record cor[+] (A : Set) {{_ : has[+] A}} : Set where
  field
    +-lunit : ∀ (x : A) → zero + x ≡ x
    +-runit : ∀ (x  : A) → x + zero ≡ x
    +-assoc : ∀ (x y z : A) → x + (y + z) ≡ x + y + z
    +-commu : ∀ (x y : A) → x + y ≡ y + x
open cor[+] {{...}} public

{-# DISPLAY cor[+].+-lunit _ = +-lunit #-}
{-# DISPLAY cor[+].+-runit _ = +-runit #-}
{-# DISPLAY cor[+].+-assoc _ = +-assoc #-}
{-# DISPLAY cor[+].+-commu _ = +-commu #-}

-- rings --

record has[*] (A : Set) {{_ : has[+] A}} : Set where
  infixl 16 _*_
  field
    one : A
    _*_ : A → A → A
open has[*] {{...}} public

{-# DISPLAY has[*].one _ = one #-}
{-# DISPLAY has[*]._*_ _ = _*_ #-}

record cor[*] (A : Set) {{_ : has[+] A}} {{_ : cor[+] A}} {{_ : has[*] A}} : Set where
  field
    *-lzero : ∀ (x : A) → zero * x ≡ zero
    *-rzero : ∀ (x : A) → x * zero ≡ zero
    *-lunit : ∀ (x : A) → one * x ≡ x
    *-runit : ∀ (x : A) → x * one ≡ x
    *-assoc : ∀ (x y z : A) → x * (y * z) ≡ x * y * z
    *-commu : ∀ (x y : A) → x * y ≡ y * x
    *-ldist : ∀ (x y z : A) → x * (y + z) ≡ x * y + x * z
    *-rdist : ∀ (x y z : A) → (x + y) * z ≡ x * z + y * z
open cor[*] {{...}} public

{-# DISPLAY cor[*].*-lzero _ = *-lzero #-}
{-# DISPLAY cor[*].*-rzero _ = *-rzero #-}
{-# DISPLAY cor[*].*-lunit _ = *-lunit #-}
{-# DISPLAY cor[*].*-runit _ = *-runit #-}
{-# DISPLAY cor[*].*-assoc _ = *-assoc #-}
{-# DISPLAY cor[*].*-commu _ = *-commu #-}
{-# DISPLAY cor[*].*-ldist _ = *-ldist #-}
{-# DISPLAY cor[*].*-rdist _ = *-rdist #-}

-- total order --

record has[<] (A : Set) : Set₁ where
  infix 10 _<_ _≤_
  field
    _<_ : A → A → Set
    _≤_ : A → A → Set
open has[<] {{...}} public

{-# DISPLAY has[<]._<_ _ = _<_ #-}
{-# DISPLAY has[<]._≤_ _ = _≤_ #-}

record cor[<] (A : Set) {{_ : has[<] A}} : Set₁ where
  field
    <-irref : ∀ (x : A) → ¬ x < x
    <-trans : ∀ (x y z : A) → x < y → y < z → x < z
    ≤-intro : ∀ (x y : A) → ¬ y < x → x ≤ y
    ≤-split : ∀ (x y : A) → x ≤ y → x < y ∨ x ≡ y
  <-asymm : ∀ (x y : A) → x < y → ¬ y < x
  <-asymm x y ε₁ ε₂ = <-irref x (<-trans x y x ε₁ ε₂)
  <-weaken : ∀ (x y : A) → x < y → x ≤ y
  <-weaken x y ε = ≤-intro x y (<-asymm x y ε)
  ≤-refl : ∀ (x : A) → x ≤ x
  ≤-refl x = ≤-intro x x (<-irref x)
  ≤-refl-≡ : ∀ (x y : A) → x ≡ y → x ≤ y
  ≤-refl-≡ x _ refl = ≤-refl x
  ≤-trans : ∀ (x y z : A) → x ≤ y → y ≤ z → x ≤ z
  ≤-trans x y z ε₁ ε₂ with ≤-split x y ε₁ | ≤-split y z ε₂
  … | Inl ε | Inl ε′ = ≤-intro x z λ ε″ → <-asymm z x ε″ (<-trans x y z ε ε′)
  … | Inl _ | Inr refl = ε₁
  … | Inr refl | Inl _ = ε₂
  … | Inr refl | Inr refl = ≤-refl x
  ≤-antisym : ∀ (x y : A) → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym x y ε₁ ε₂ with ≤-split x y ε₁ | ≤-split y x ε₂
  … | Inr refl | _        = refl
  … | _        | Inr refl = refl
  … | Inl ε    | Inl ε′ = absurd (<-asymm x y ε ε′)
  <-ltrans : ∀ (x y z : A) → x ≤ y → y < z → x < z
  <-ltrans x y z ε₁ ε₂ with ≤-split x y ε₁
  … | Inl ε = <-trans x y z ε ε₂
  … | Inr refl = ε₂
  <-rtrans : ∀ (x y z : A) → x < y → y ≤ z → x < z
  <-rtrans x y z ε₁ ε₂ with ≤-split y z ε₂
  … | Inl ε = <-trans x y z ε₁ ε
  … | Inr refl = ε₁
open cor[<] {{...}} public

{-# DISPLAY cor[<].<-irref _ = <-irref  #-}
{-# DISPLAY cor[<].<-trans _ = <-trans  #-}
{-# DISPLAY cor[<].<-asymm _ = <-asymm  #-}
{-# DISPLAY cor[<].≤-intro   _ = ≤-intro   #-}
{-# DISPLAY cor[<].≤-split   _ = ≤-split   #-}
{-# DISPLAY cor[<].<-weaken  _ = <-weaken  #-}
{-# DISPLAY cor[<].≤-refl    _ = ≤-refl    #-}
{-# DISPLAY cor[<].≤-antisym _ = ≤-antisym #-}
{-# DISPLAY cor[<].<-ltrans  _ = <-ltrans  #-}
{-# DISPLAY cor[<].<-rtrans  _ = <-rtrans  #-}

-- comparison --

data Comp[∇] : Set where
  LT : Comp[∇]
  EQ : Comp[∇]
  GT : Comp[∇]

data Comp[<] : Set where
  LT : Comp[<]
  GE : Comp[<]

data Comp[≤] : Set where
  LE : Comp[≤]
  GT : Comp[≤]

data Comp[≡] : Set where
  EQ : Comp[≡]
  NE : Comp[≡]

record has[<?] (A : Set) : Set where
  infix 14 _∇?_ _<?_ _≤?_  _≡?_
  field
    _∇?_ : A → A → Comp[∇]
  _<?_ : A → A → Comp[<]
  x <? y with x ∇? y
  … | LT = LT
  … | EQ = GE
  … | GT = GE
  _≤?_ : A → A → Comp[≤]
  x ≤? y with x ∇? y
  … | LT = LE
  … | EQ = LE
  … | GT = GT
  _≡?_ : A → A → Comp[≡]
  x ≡? y with x ∇? y
  … | LT = NE
  … | EQ = EQ
  … | GT = NE
  
open has[<?] {{...}} public

{-# DISPLAY has[<?]._∇?_ _ = _∇?_ #-}
{-# DISPLAY has[<?]._<?_ _ = _<?_ #-}
{-# DISPLAY has[<?]._≤?_ _ = _≤?_ #-}
{-# DISPLAY has[<?]._≡?_ _ = _≡?_ #-}

data Ord[∇][_] {A : Set} (_≺_ : A → A → Set) (x y : A) : Set where
  LT : x ≺ y → Ord[∇][ _≺_ ] x y
  EQ : x ≡ y → Ord[∇][ _≺_ ] x y
  GT : y ≺ x → Ord[∇][ _≺_ ] x y

data Link[∇][_] {A : Set} (_≺_ : A → A → Set) {x y : A} : Comp[∇] → Ord[∇][ _≺_ ] x y → Set where
  LT : ∀ {ε : x ≺ y} → Link[∇][ _≺_ ] LT (LT ε)
  EQ : ∀ {ε : x ≡ y} → Link[∇][ _≺_ ] EQ (EQ ε)
  GT : ∀ {ε : y ≺ x} → Link[∇][ _≺_ ] GT (GT ε)

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

data Ord[≡] {A : Set} (x y : A) : Set where
  EQ : x ≡ y → Ord[≡] x y
  NE : ¬ x ≡ y → Ord[≡] x y

data Link[≡] {A : Set} {x y : A} : Comp[≡] → Ord[≡] x y → Set where
  EQ : ∀ {ε : x ≡ y} → Link[≡] EQ (EQ ε)
  NE : ∀ {ε : ¬ x ≡ y} → Link[≡] NE (NE ε)

record cor[<?] (A : Set) {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} : Set₁ where
  field
    _∇*_ : ∀ (x y : A) → Ord[∇][ _<_ ] x y
    _∇~_ : ∀ (x y : A) → Link[∇][ _<_ ] (x ∇? y) (x ∇* y)
  _<*_ : ∀ (x y : A) → Ord[<][ _≤_ , _<_ ] x y
  x <* y with x ∇* y
  … | LT ε = LT ε
  … | EQ ε = GE (≤-refl-≡ y x (sym ε))
  … | GT ε = GE (<-weaken y x ε)
  _<~_ : ∀ (x y : A) → Link[<][ _≤_ , _<_ ] (x <? y) (x <* y)
  x <~ y with x ∇? y | x ∇* y | x ∇~ y
  … | LT | LT _ | LT = LT
  … | EQ | EQ _ | EQ = GE
  … | GT | GT _ | GT = GE
  _≤*_ : ∀ (x y : A) → Ord[≤][ _≤_ , _<_ ] x y
  x ≤* y with x ∇* y
  … | LT ε = LE (<-weaken x y ε)
  … | EQ ε = LE (≤-refl-≡ x y ε)
  … | GT ε = GT ε
  _≤~_ : ∀ (x y : A) → Link[≤][ _≤_ , _<_ ] (x ≤? y) (x ≤* y)
  x ≤~ y with x ∇? y | x ∇* y | x ∇~ y
  … | LT | LT _ | LT = LE
  … | EQ | EQ _ | EQ = LE
  … | GT | GT _ | GT = GT
  _≡*_ : ∀ (x y : A) → Ord[≡] x y
  x ≡* y with x ∇* y
  … | LT ε = NE λ where refl → <-irref x ε
  … | EQ ε = EQ ε
  … | GT ε = NE λ where refl → <-irref x ε
  _≡~_ : ∀ (x y : A) → Link[≡] (x ≡? y) (x ≡* y)
  x ≡~ y with x ∇? y | x ∇* y | x ∇~ y
  … | LT | LT _ | LT = NE
  … | EQ | EQ _ | EQ = EQ
  … | GT | GT _ | GT = NE
open cor[<?] {{...}} public

{-# DISPLAY cor[<?]._∇*_ _ = _∇*_ #-}
{-# DISPLAY cor[<?]._∇~_ _ = _∇~_ #-}
{-# DISPLAY cor[<?]._<*_ _ = _<*_ #-}
{-# DISPLAY cor[<?]._<~_ _ = _<~_ #-}
{-# DISPLAY cor[<?]._≤*_ _ = _≤*_ #-}
{-# DISPLAY cor[<?]._≤~_ _ = _≤~_ #-}
{-# DISPLAY cor[<?]._≡*_ _ = _≡*_ #-}
{-# DISPLAY cor[<?]._≡~_ _ = _≡~_ #-}

-- ===== --
-- bools --
-- ===== --

data 𝔹 : Set where
  True : 𝔹
  False : 𝔹

-- =============== --
-- natural numbers --
-- =============== --

data ℕ : Set where
  Zero : ℕ
  Suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

----------------
-- operations --
----------------

_+ᴺ_ : ℕ → ℕ → ℕ
Zero    +ᴺ n  =  n
(Suc m) +ᴺ n  =  Suc (m +ᴺ n)

_*ᴺ_ : ℕ → ℕ → ℕ
Zero *ᴺ n     =  Zero
(Suc m) *ᴺ n  =  n +ᴺ (m *ᴺ n)

_∸ᴺ_ : ℕ → ℕ → ℕ
m       ∸ᴺ Zero     =  m
Zero    ∸ᴺ (Suc n)  =  Zero
(Suc m) ∸ᴺ (Suc n)  =  m ∸ᴺ n

instance
  has[++][ℕ] : has[++] ℕ
  has[++][ℕ] = record { null = 0 ; _++_ = _+ᴺ_ }
  has[+][ℕ] : has[+] ℕ
  has[+][ℕ] = record { zero = 0 ; _+_ = _+ᴺ_ }
  has[*][ℕ] : has[*] ℕ
  has[*][ℕ] = record { one = 1 ; _*_ = _*ᴺ_}

----------
-- laws --
----------

-- plus --

+ᴺ-lunit : ∀ (m : ℕ) → Zero +ᴺ m ≡ m
+ᴺ-lunit m = refl

+ᴺ-runit : ∀ (m : ℕ) → m +ᴺ Zero ≡ m
+ᴺ-runit Zero = refl
+ᴺ-runit (Suc m) rewrite +ᴺ-runit m = refl

+ᴺ-rsuc : ∀ (m n : ℕ) → m +ᴺ Suc n ≡ Suc (m +ᴺ n)
+ᴺ-rsuc Zero n = refl
+ᴺ-rsuc (Suc m) n rewrite +ᴺ-rsuc m n = refl

+ᴺ-assoc : ∀ (m n p : ℕ) → m +ᴺ (n +ᴺ p) ≡ m +ᴺ n +ᴺ p
+ᴺ-assoc Zero n p = refl
+ᴺ-assoc (Suc m) n p rewrite +ᴺ-assoc m n p = refl

+ᴺ-commu : ∀ (m n : ℕ) → m +ᴺ n ≡ n +ᴺ m
+ᴺ-commu Zero n rewrite +ᴺ-runit n = refl
+ᴺ-commu (Suc m) n rewrite +ᴺ-rsuc n m | +ᴺ-commu m n = refl

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

*ᴺ-lzero : ∀ (m : ℕ) → Zero *ᴺ m ≡ Zero
*ᴺ-lzero m = refl

*ᴺ-rzero : ∀ (m : ℕ) → m *ᴺ Zero ≡ Zero
*ᴺ-rzero Zero = refl
*ᴺ-rzero (Suc m) rewrite *ᴺ-rzero m = refl

*ᴺ-lunit : ∀ (m : ℕ) → one *ᴺ m ≡ m
*ᴺ-lunit m rewrite +ᴺ-runit m = refl

*ᴺ-runit : ∀ (m : ℕ) → m *ᴺ 1 ≡ m
*ᴺ-runit Zero = refl
*ᴺ-runit (Suc m) rewrite *ᴺ-runit m = refl

*ᴺ-rsuc : ∀ (m n : ℕ) → m *ᴺ Suc n ≡ m +ᴺ m *ᴺ n
*ᴺ-rsuc Zero n = refl
*ᴺ-rsuc (Suc m) n
  rewrite *ᴺ-rsuc m n
        | +ᴺ-assoc n m (m *ᴺ n)
        | +ᴺ-assoc m n (m *ᴺ n)
        | +ᴺ-commu m n 
        = refl

*ᴺ-rdist : ∀ (m n p : ℕ) → (m +ᴺ n) *ᴺ p ≡ (m *ᴺ p) +ᴺ (n *ᴺ p)
*ᴺ-rdist Zero n p = refl
*ᴺ-rdist (Suc m) n p rewrite *ᴺ-rdist m n p | +ᴺ-assoc p (m *ᴺ p) (n *ᴺ p) = refl

*ᴺ-assoc : ∀ (m n p : ℕ) → m *ᴺ (n *ᴺ p) ≡ m *ᴺ n *ᴺ p
*ᴺ-assoc Zero n p = refl
*ᴺ-assoc (Suc m) n p rewrite *ᴺ-rdist n (m *ᴺ n) p | *ᴺ-assoc m n p = refl

*ᴺ-commu : ∀ (m n : ℕ) → m *ᴺ n ≡ n *ᴺ m
*ᴺ-commu Zero n rewrite *ᴺ-rzero n = refl
*ᴺ-commu (Suc m) n rewrite *ᴺ-commu m n | *ᴺ-rsuc n m = refl

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

data _<ᴺ_ : ℕ → ℕ → Set where
  Zero : ∀ {n : ℕ}
    → Zero <ᴺ Suc n
  Suc : ∀ {m n : ℕ}
    → m <ᴺ n
    → Suc m <ᴺ Suc n

data _≤ᴺ_ : ℕ → ℕ → Set where
  Zero : ∀ {n : ℕ} → Zero ≤ᴺ n
  Suc : ∀ {m n : ℕ} → m ≤ᴺ n → Suc m ≤ᴺ Suc n

instance
  has[<][ℕ] : has[<] ℕ
  has[<][ℕ] = record { _<_ = _<ᴺ_ ; _≤_ = _≤ᴺ_ }

≤-to-< : ∀ {m n : ℕ} → m ≤ n → m < Suc n
≤-to-< Zero = Zero
≤-to-< (Suc ε) = Suc (≤-to-< ε)

<-to-≤ : ∀ {m n : ℕ} → m < n → Suc m ≤ n
<-to-≤ Zero = Suc Zero
<-to-≤ (Suc ε) = Suc (<-to-≤ ε)

≤-fr-< : ∀ {m n : ℕ} → m < Suc n → m ≤ n
≤-fr-< Zero = Zero
≤-fr-< (Suc ε) = <-to-≤ ε

<-fr-≤ : ∀ {m n : ℕ} → Suc m ≤ n → m < n
<-fr-≤ (Suc ε) = ≤-to-< ε

<ᴺ-irref : ∀ (m : ℕ) → ¬ (m <ᴺ m)
<ᴺ-irref Zero ()
<ᴺ-irref (Suc m) (Suc ε) = <ᴺ-irref m ε

<ᴺ-trans : ∀ (m n p : ℕ) → m <ᴺ n → n <ᴺ p → m <ᴺ p
<ᴺ-trans _ _ _ Zero (Suc ε₂) = Zero
<ᴺ-trans _ _ _ (Suc ε₁) (Suc ε₂) = Suc (<ᴺ-trans _ _ _ ε₁ ε₂)

<ᴺ-intro : ∀ (m n : ℕ) → ¬ n < m → m ≤ n
<ᴺ-intro Zero n ε = Zero
<ᴺ-intro (Suc m) Zero ε = absurd (ε Zero)
<ᴺ-intro (Suc m) (Suc n) ε = Suc (<ᴺ-intro m n λ where ε′ → ε (Suc ε′))

<ᴺ-split : ∀ (m n : ℕ) → m ≤ n → m < n ∨ m ≡ n
<ᴺ-split Zero Zero Zero = Inr refl
<ᴺ-split Zero (Suc n) Zero = Inl Zero
<ᴺ-split (Suc m) Zero ()
<ᴺ-split (Suc m) (Suc n) (Suc ε) with <ᴺ-split m n ε
… | Inl ε′ = Inl (Suc ε′)
… | Inr ε′ rewrite ε′ = Inr refl

instance
  cor[<][ℕ] : cor[<] ℕ
  cor[<][ℕ] = record
    { <-irref = <ᴺ-irref
    ; <-trans = <ᴺ-trans
    ; ≤-intro = <ᴺ-intro
    ; ≤-split = <ᴺ-split
    }

<ᴺ-rmono : ∀ (m n p : ℕ) → m < n → m < n + p
<ᴺ-rmono _ _ p Zero = Zero
<ᴺ-rmono _ _ p (Suc ε) = Suc (<ᴺ-rmono _ _ p ε)

<ᴺ-lmono : ∀ (m n p : ℕ) → m < p → m < n + p
<ᴺ-lmono m n p ε rewrite +-commu n p = <ᴺ-rmono m p n ε

----------------
-- comparison --
----------------

_∇?ᴺ_ : ℕ → ℕ → Comp[∇]
Zero ∇?ᴺ Zero = EQ
Zero ∇?ᴺ Suc n = LT
Suc m ∇?ᴺ Zero = GT
Suc m ∇?ᴺ Suc n = m ∇?ᴺ n

_∇*ᴺ_ : ∀ (m n : ℕ) → Ord[∇][ _<ᴺ_ ] m n
Zero ∇*ᴺ Zero = EQ refl
Zero ∇*ᴺ Suc n = LT Zero
Suc m ∇*ᴺ Zero = GT Zero
Suc m ∇*ᴺ Suc n with m ∇*ᴺ n
… | LT ε = LT (Suc ε)
… | EQ ε rewrite ε = EQ refl
… | GT ε = GT (Suc ε)

_∇~ᴺ_ : ∀ (m n : ℕ) → Link[∇][ _<ᴺ_ ] (m ∇?ᴺ n) (m ∇*ᴺ n)
Zero ∇~ᴺ Zero = EQ
Zero ∇~ᴺ Suc n = LT
Suc m ∇~ᴺ Zero = GT
Suc m ∇~ᴺ Suc n with m ∇?ᴺ n | m ∇*ᴺ n | m ∇~ᴺ n
… | LT | LT ε | LT = LT
… | EQ | EQ ε | EQ rewrite ε = EQ
… | GT | GT ε | GT = GT

instance
  has[<?][ℕ] : has[<?] ℕ
  has[<?][ℕ] = record { _∇?_ = _∇?ᴺ_}
  cor[<?][ℕ] : cor[<?] ℕ
  cor[<?][ℕ] = record
    { _∇*_ = _∇*ᴺ_
    ; _∇~_ = _∇~ᴺ_
    }

-- ===== --
-- Lists --
-- ===== --

data list (A : Set) : Set where
  [] : list A
  _∷_ : A → list A → list A

pattern l[_] a = a ∷ []
pattern l[_,_] a b = a ∷ l[ b ]
pattern l[_,_,_] a b c = a ∷ l[ b , c ]
pattern l[_,_,_,_] a b c d = a ∷ l[ b , c , d ]
pattern l[_,_,_,_,_] a b c d e = a ∷ l[ b , c , d , e ]
pattern l[_,_,_,_,_,_] a b c d e f = a ∷ l[ b , c , d , e , f ]
pattern l[_,_,_,_,_,_,_] a b c d e f g = a ∷ l[ b , c , d , e , f , g ]
pattern l[_,_,_,_,_,_,_,_] a b c d e f g h = a ∷ l[ b , c , d , e , f , g , h ]
pattern l[_,_,_,_,_,_,_,_,_] a b c d e f g h i = a ∷ l[ b , c , d , e , f , g , h , i ]
pattern l[_,_,_,_,_,_,_,_,_,_] a b c d e f g h i j = a ∷ l[ b , c , d , e , f , g , h , i , j ]

------------
-- monoid --
------------

_++ᴸ_ : ∀ {A : Set} → list A → list A → list A
[] ++ᴸ ys = ys
(x ∷ xs) ++ᴸ ys = x ∷ (xs ++ᴸ ys)

instance
  has[++][list] : ∀ {A : Set} → has[++] (list A)
  has[++][list] = record { null = [] ; _++_ = _++ᴸ_ }

++ᴸ-lunit : ∀ {A : Set} (xs : list A) → [] ++ᴸ xs ≡ xs
++ᴸ-lunit xs = refl

++ᴸ-runit : ∀ {A : Set} (xs : list A) → xs ++ᴸ [] ≡ xs
++ᴸ-runit [] = refl
++ᴸ-runit (x ∷ xs) rewrite ++ᴸ-runit xs = refl

++ᴸ-assoc : ∀ {A : Set} (xs ys zs : list A) → xs ++ᴸ (ys ++ᴸ zs) ≡ xs ++ᴸ ys ++ᴸ zs
++ᴸ-assoc [] ys zs = refl
++ᴸ-assoc (x ∷ xs) ys zs rewrite ++ᴸ-assoc xs ys zs = refl

instance
  cor[++][list] : ∀ {A : Set} → cor[++] (list A)
  cor[++][list] = record { ++-lunit = ++ᴸ-lunit ; ++-runit = ++ᴸ-runit ; ++-assoc = ++ᴸ-assoc }

----------------------
-- other operations --
----------------------

length : ∀ {A : Set} → list A → ℕ
length [] = Zero
length (x ∷ xs) = Suc (length xs)

map : ∀ {A B : Set} → (A → B) → list A → list B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {A B : Set} → (A → B → B) → B → list A → B
foldr f i [] = i
foldr f i (x ∷ xs) = f x (foldr f i xs)

foldl : ∀ {A B : Set} → (A → B → B) → B → list A → B
foldl f i [] = i
foldl f i (x ∷ xs) = foldl f (f x i) xs

-- ====== --
-- Option --
-- ====== --

data option (A : Set) : Set where
  None : option A
  Some : A → option A
