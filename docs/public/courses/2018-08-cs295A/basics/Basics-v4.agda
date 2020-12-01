{-# OPTIONS --experimental-irrelevance #-}
module Basics-v4 where

infixl 0 AT-TYPE
infixr 1 CASE_OF_
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

irr-≡ : ∀ {A : Set} {x y : A} → .(x ≡ y) → x ≡ y
irr-≡ refl = refl

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

abstract
  instance
    block : 𝟙
    block = TT
  unblock : block ≡ TT
  unblock = refl

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

-- ascription --

syntax AT-TYPE A x = x AT A
AT-TYPE : ∀ (A : Set) → A → A
AT-TYPE _ x = x

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
  infix 10 _≤_
  infix 10 _<_
  field
    _<_ : A → A → Set
    _≤_ : A → A → Set
open has[<] {{...}} public

{-# DISPLAY has[<]._<_ _ = _<_ #-}
{-# DISPLAY has[<]._≤_ _ = _≤_ #-}

record cor[<] (A : Set) {{_ : has[<] A}} : Set₁ where
  field
    ≤-refl : ∀ (x : A) → x ≤ x
    ≤-trans : ∀ (x y z : A) → x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : ∀ (x y : A) → x ≤ y → y ≤ x → x ≡ y
    <-irrefl : ∀ (x : A) → ¬ x < x
    <-trans : ∀ (x y z : A) → x < y → y < z → x < z
    <-ltrans : ∀ (x y z : A) → x ≤ y → y < z → x < z
    <-rtrans : ∀ (x y z : A) → x < y → y ≤ z → x < z
    <-asym : ∀ (x y : A) → x < y → ¬ y < x
    <-weaken : ∀ (x y : A) → x < y → x ≤ y
    <-splits : ∀ (x y : A) → x ≤ y → x < y ∨ x ≡ y
open cor[<] {{...}} public

{-# DISPLAY cor[<].≤-refl    _ = ≤-refl    #-}
{-# DISPLAY cor[<].≤-trans   _ = ≤-trans   #-}
{-# DISPLAY cor[<].≤-antisym _ = ≤-antisym #-}
{-# DISPLAY cor[<].<-irrefl  _ = <-irrefl  #-}
{-# DISPLAY cor[<].<-trans   _ = <-trans   #-}
{-# DISPLAY cor[<].<-ltrans  _ = <-ltrans  #-}
{-# DISPLAY cor[<].<-rtrans  _ = <-rtrans  #-}
{-# DISPLAY cor[<].<-asym    _ = <-asym    #-}
{-# DISPLAY cor[<].<-weaken  _ = <-weaken  #-}
{-# DISPLAY cor[<].<-splits  _ = <-splits  #-}

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} where
  ≤-refl-≡ : ∀ (x y : A) → x ≡ y → x ≤ y
  ≤-refl-≡ x .x refl = ≤-refl x

-- comparison --

data comp[≡] : Set where
  EQ : comp[≡]
  NE : comp[≡]

data comp[≤] : Set where
  LE : comp[≤]
  GT : comp[≤]

data comp[<] : Set where
  LT : comp[<]
  GE : comp[<]

data comp[∇] : Set where
  LT : comp[∇]
  EQ : comp[∇]
  GT : comp[∇]

record has[<?] (A : Set) : Set where
  infix 14 _∇?_ _≤?_ _<?_
  field
    _≡?_ : A → A → comp[≡]
    _<?_ : A → A → comp[<]
    _≤?_ : A → A → comp[≤]
    _∇?_ : A → A → comp[∇]
open has[<?] {{...}} public

{-# DISPLAY has[<?]._≡?_ _ = _≡?_ #-}
{-# DISPLAY has[<?]._<?_ _ = _<?_ #-}
{-# DISPLAY has[<?]._≤?_ _ = _≤?_ #-}
{-# DISPLAY has[<?]._∇?_ _ = _∇?_ #-}

data ord[≡] {A : Set} (x y : A) : Set where
  EQ : x ≡ y → ord[≡] x y
  NE : ¬ x ≡ y → ord[≡] x y

data link[≡] {A : Set} {x y : A} : comp[≡] → ord[≡] x y → Set where
  EQ : ∀ {ε : x ≡ y} → link[≡] EQ (EQ ε)
  NE : ∀ {ε : ¬ x ≡ y} → link[≡] NE (NE ε)

data ord[<][_,_] {A : Set} (_≼_ : A → A → Set) (_≺_ : A → A → Set) (x y : A) : Set where
  LT : x ≺ y → ord[<][ _≼_ , _≺_ ] x y
  GE : y ≼ x → ord[<][ _≼_ , _≺_ ] x y

data link[<][_,_] {A : Set} (_≼_ : A → A → Set) (_≺_ : A → A → Set) {x y : A} : comp[<] → ord[<][ _≼_ , _≺_ ] x y → Set where
  LT : ∀ {ε : x ≺ y} → link[<][ _≼_ , _≺_ ] LT (LT ε)
  GE : ∀ {ε : y ≼ x} → link[<][ _≼_ , _≺_ ] GE (GE ε)

data ord[≤][_,_] {A : Set} (_≼_ : A → A → Set) (_≺_ : A → A → Set) (x y : A) : Set where
  LE : x ≼ y → ord[≤][ _≼_ , _≺_ ] x y
  GT : y ≺ x → ord[≤][ _≼_ , _≺_ ] x y

data link[≤][_,_] {A : Set} (_≼_ : A → A → Set) (_≺_ : A → A → Set) {x y : A} : comp[≤] → ord[≤][ _≼_ , _≺_ ] x y → Set where
  LE : ∀ {ε : x ≼ y} → link[≤][ _≼_ , _≺_ ] LE (LE ε)
  GT : ∀ {ε : y ≺ x} → link[≤][ _≼_ , _≺_ ] GT (GT ε)

data ord[∇][_] {A : Set} (_≺_ : A → A → Set) (x y : A) : Set where
  LT : x ≺ y → ord[∇][ _≺_ ] x y
  EQ : x ≡ y → ord[∇][ _≺_ ] x y
  GT : y ≺ x → ord[∇][ _≺_ ] x y

data link[∇][_] {A : Set} (_≺_ : A → A → Set) {x y : A} : comp[∇] → ord[∇][ _≺_ ] x y → Set where
  LT : ∀ {ε : x ≺ y} → link[∇][ _≺_ ] LT (LT ε)
  EQ : ∀ {ε : x ≡ y} → link[∇][ _≺_ ] EQ (EQ ε)
  GT : ∀ {ε : y ≺ x} → link[∇][ _≺_ ] GT (GT ε)

record cor[<?] (A : Set) {{_ : has[<] A}} {{_ : has[<?] A}} : Set₁ where
  field
    _≡*_ : ∀ (x y : A) → ord[≡] x y
    _≡~_ : ∀ (x y : A) → link[≡] (x ≡? y) (x ≡* y)
    _<*_ : ∀ (x y : A) → ord[<][ _≤_ , _<_ ] x y
    _<~_ : ∀ (x y : A) → link[<][ _≤_ , _<_ ] (x <? y) (x <* y)
    _≤*_ : ∀ (x y : A) → ord[≤][ _≤_ , _<_ ] x y
    _≤~_ : ∀ (x y : A) → link[≤][ _≤_ , _<_ ] (x ≤? y) (x ≤* y)
    _∇*_ : ∀ (x y : A) → ord[∇][ _<_ ] x y
    _∇~_ : ∀ (x y : A) → link[∇][ _<_ ] (x ∇? y) (x ∇* y)
open cor[<?] {{...}} public

{-# DISPLAY cor[<?]._≡*_ _ = _≡*_ #-}
{-# DISPLAY cor[<?]._≡~_ _ = _≡~_ #-}
{-# DISPLAY cor[<?]._<*_ _ = _<*_ #-}
{-# DISPLAY cor[<?]._<~_ _ = _<~_ #-}
{-# DISPLAY cor[<?]._≤*_ _ = _≤*_ #-}
{-# DISPLAY cor[<?]._≤~_ _ = _≤~_ #-}
{-# DISPLAY cor[<?]._∇*_ _ = _∇*_ #-}
{-# DISPLAY cor[<?]._∇~_ _ = _∇~_ #-}

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where
  ≤?≡LE : ∀ (x y : A) → x ≤ y → x ≤? y ≡ LE
  ≤?≡LE x y ε with x ≤? y | x ≤* y | x ≤~ y
  … | LE | LE _ | LE = refl
  … | GT | GT ε′ | GT with <-splits x y ε
  … | Inl ε″ = absurd (<-asym x  y ε″ ε′)
  … | Inr refl = absurd (<-irrefl x ε′)

  ≤?≡GT : ∀ (x y : A) → y < x → x ≤? y ≡ GT
  ≤?≡GT x y ε with x ≤? y | x ≤* y | x ≤~ y
  … | GT | GT _ | GT = refl
  … | LE | LE ε′ | LE with <-splits x y ε′
  … | Inl ε″ = absurd (<-asym x y ε″ ε)
  … | Inr refl = absurd (<-irrefl x ε)

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

data _≤ᴺ_ : ℕ → ℕ → Set where
  Zero : ∀ {n : ℕ} → Zero ≤ᴺ n
  Suc : ∀ {m n : ℕ} → m ≤ᴺ n → Suc m ≤ᴺ Suc n

data _<ᴺ_ : ℕ → ℕ → Set where
  Zero : ∀ {n : ℕ}
    → Zero <ᴺ Suc n
  Suc : ∀ {m n : ℕ}
    → m <ᴺ n
    → Suc m <ᴺ Suc n

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

≤ᴺ-refl : ∀ (m : ℕ) → m ≤ᴺ m
≤ᴺ-refl Zero = Zero
≤ᴺ-refl (Suc m) = Suc (≤ᴺ-refl m)

≤ᴺ-trans : ∀ (m n p : ℕ) → m ≤ᴺ n → n ≤ᴺ p → m ≤ᴺ p
≤ᴺ-trans _ _ _ Zero ε₁ = Zero
≤ᴺ-trans _ _ _ (Suc ε₁) (Suc ε₂) = Suc (≤ᴺ-trans _ _ _ ε₁ ε₂)

≤ᴺ-antisym : ∀ (m n : ℕ) → m ≤ᴺ n → n ≤ᴺ m → m ≡ n
≤ᴺ-antisym _ _ Zero Zero = refl
≤ᴺ-antisym _ _ (Suc ε₁) (Suc ε₂) rewrite ≤ᴺ-antisym _ _ ε₁ ε₂ = refl

<ᴺ-irrefl : ∀ (m : ℕ) → ¬ (m <ᴺ m)
<ᴺ-irrefl Zero ()
<ᴺ-irrefl (Suc m) (Suc ε) = <ᴺ-irrefl m ε

<ᴺ-ltrans : ∀ (m n p : ℕ) → m ≤ᴺ n → n <ᴺ p → m <ᴺ p
<ᴺ-ltrans _ _ _ Zero Zero = Zero
<ᴺ-ltrans _ _ _ Zero (Suc ε₂) = Zero
<ᴺ-ltrans _ _ _ (Suc ε₁) (Suc ε₂) = Suc (<ᴺ-ltrans _ _ _ ε₁ ε₂)

<ᴺ-rtrans : ∀ (m n p : ℕ) → m <ᴺ n → n ≤ᴺ p → m <ᴺ p
<ᴺ-rtrans _ _ _ Zero (Suc ε₂) = Zero
<ᴺ-rtrans _ _ _ (Suc ε₁) (Suc ε₂) = Suc (<ᴺ-rtrans _ _ _ ε₁ ε₂)

<ᴺ-weaken : ∀ (m n : ℕ) → m < n → m ≤ n
<ᴺ-weaken _ _ Zero = Zero
<ᴺ-weaken _ _ (Suc ε) = Suc (<ᴺ-weaken _ _ ε)

<ᴺ-trans : ∀ (m n p : ℕ) → m <ᴺ n → n <ᴺ p → m <ᴺ p
<ᴺ-trans _ _ _ ε₁ ε₂ = <ᴺ-ltrans _ _ _ (<ᴺ-weaken _ _ ε₁) ε₂

<ᴺ-asym : ∀ (m n : ℕ) → m <ᴺ n → ¬ n <ᴺ m
<ᴺ-asym m n ε₁ ε₂ = <ᴺ-irrefl n (<ᴺ-trans _ _ _ ε₂ ε₁)

<ᴺ-splits : ∀ (m n : ℕ) → m ≤ n → m < n ∨ m ≡ n
<ᴺ-splits Zero Zero Zero = Inr refl
<ᴺ-splits Zero (Suc n) Zero = Inl Zero
<ᴺ-splits (Suc m) Zero ()
<ᴺ-splits (Suc m) (Suc n) (Suc ε) with <ᴺ-splits m n ε
… | Inl ε′ = Inl (Suc ε′)
… | Inr ε′ rewrite ε′ = Inr refl

instance
  cor[<][ℕ] : cor[<] ℕ
  cor[<][ℕ] = record
    { ≤-refl = ≤ᴺ-refl
    ; ≤-trans = ≤ᴺ-trans
    ; ≤-antisym = ≤ᴺ-antisym
    ; <-irrefl = <ᴺ-irrefl
    ; <-trans = <ᴺ-trans
    ; <-ltrans = <ᴺ-ltrans
    ; <-rtrans = <ᴺ-rtrans
    ; <-asym = <ᴺ-asym
    ; <-weaken = <ᴺ-weaken
    ; <-splits = <ᴺ-splits
    }

<ᴺ-rmono : ∀ (m n p : ℕ) → m < n → m < n + p
<ᴺ-rmono _ _ p Zero = Zero
<ᴺ-rmono _ _ p (Suc ε) = Suc (<ᴺ-rmono _ _ p ε)

<ᴺ-lmono : ∀ (m n p : ℕ) → m < p → m < n + p
<ᴺ-lmono m n p ε rewrite +-commu n p = <ᴺ-rmono m p n ε

----------------
-- comparison --
----------------

_≡?ᴺ_ : ℕ → ℕ → comp[≡]
Zero ≡?ᴺ Zero = EQ
Zero ≡?ᴺ Suc y = NE
Suc x ≡?ᴺ Zero = NE
Suc x ≡?ᴺ Suc y = x ≡?ᴺ y 

_≡*ᴺ_ : ∀ (x y : ℕ) → ord[≡] x y
Zero ≡*ᴺ Zero = EQ refl
Zero ≡*ᴺ Suc y = NE (λ ())
Suc x ≡*ᴺ Zero = NE (λ ())
Suc x ≡*ᴺ Suc y with x ≡*ᴺ y
… | EQ ε rewrite ε = EQ refl
… | NE ε = NE λ where refl → ε refl

_≡~ᴺ_ : ∀ (x y : ℕ) → link[≡] (x ≡?ᴺ y) (x ≡*ᴺ y)
Zero ≡~ᴺ Zero = EQ
Zero ≡~ᴺ Suc y = NE
Suc x ≡~ᴺ Zero = NE
Suc x ≡~ᴺ Suc y with x ≡?ᴺ y | x ≡*ᴺ y | x ≡~ᴺ y
… | EQ | EQ ε | EQ rewrite ε = EQ
… | NE | NE ε | NE = NE

_<?ᴺ_ : ℕ → ℕ → comp[<]
Zero <?ᴺ Zero = GE
Zero <?ᴺ Suc n = LT
Suc m <?ᴺ Zero = GE
Suc m <?ᴺ Suc n = m <?ᴺ n

_<*ᴺ_ : ∀ (m n : ℕ) → ord[<][ _≤ᴺ_ , _<ᴺ_ ] m n
Zero <*ᴺ Zero = GE Zero
Zero <*ᴺ Suc n = LT Zero
Suc m <*ᴺ Zero = GE Zero
Suc m <*ᴺ Suc n with m <*ᴺ n
… | LT ε = LT (Suc ε)
… | GE ε = GE (Suc ε)

_<~ᴺ_ : ∀ (m n : ℕ) → link[<][ _≤ᴺ_ , _<ᴺ_ ] (m <?ᴺ n) (m <*ᴺ n)
Zero <~ᴺ Zero = GE
Zero <~ᴺ Suc n = LT
Suc m <~ᴺ Zero = GE
Suc m <~ᴺ Suc n with m <?ᴺ n | m <*ᴺ n | m <~ᴺ n
… | LT | LT ε | LT = LT
… | GE | GE ε | GE = GE

_≤?ᴺ_ : ℕ → ℕ → comp[≤]
Zero ≤?ᴺ n = LE
Suc m ≤?ᴺ Zero = GT
Suc m ≤?ᴺ Suc n = m ≤?ᴺ n

_≤*ᴺ_ : ∀ (m n : ℕ) → ord[≤][ _≤ᴺ_ , _<ᴺ_ ] m n
Zero ≤*ᴺ n = LE Zero
Suc m ≤*ᴺ Zero = GT Zero
Suc m ≤*ᴺ Suc n with m ≤*ᴺ n
… | LE ε = LE (Suc ε)
… | GT ε = GT (Suc ε)

_≤~ᴺ_ : ∀ (m n : ℕ) → link[≤][ _≤ᴺ_ , _<ᴺ_ ] (m ≤?ᴺ n) (m ≤*ᴺ n)
Zero ≤~ᴺ n = LE
Suc m ≤~ᴺ Zero = GT
Suc m ≤~ᴺ Suc n with m ≤?ᴺ n | m ≤*ᴺ n | m ≤~ᴺ n
… | LE | LE ε | LE = LE
… | GT | GT ε | GT = GT

_∇?ᴺ_ : ℕ → ℕ → comp[∇]
Zero ∇?ᴺ Zero = EQ
Zero ∇?ᴺ Suc n = LT
Suc m ∇?ᴺ Zero = GT
Suc m ∇?ᴺ Suc n = m ∇?ᴺ n

_∇*ᴺ_ : ∀ (m n : ℕ) → ord[∇][ _<ᴺ_ ] m n
Zero ∇*ᴺ Zero = EQ refl
Zero ∇*ᴺ Suc n = LT Zero
Suc m ∇*ᴺ Zero = GT Zero
Suc m ∇*ᴺ Suc n with m ∇*ᴺ n
… | LT ε = LT (Suc ε)
… | EQ ε rewrite ε = EQ refl
… | GT ε = GT (Suc ε)

_∇~ᴺ_ : ∀ (m n : ℕ) → link[∇][ _<ᴺ_ ] (m ∇?ᴺ n) (m ∇*ᴺ n)
Zero ∇~ᴺ Zero = EQ
Zero ∇~ᴺ Suc n = LT
Suc m ∇~ᴺ Zero = GT
Suc m ∇~ᴺ Suc n with m ∇?ᴺ n | m ∇*ᴺ n | m ∇~ᴺ n
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
-- Lists --
-- ===== --

data list (A : Set) : Set where
  [] : list A
  _∷_ : A → list A → list A

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

-- ====== --
-- Sorted --
-- ====== --

module _ {A : Set} {{_ : has[<] A}} where
  infix 10 _≤-head_
  data _≤-head_ (x : A) : list A → Set where
    [] : x ≤-head []
    ⟨_⟩ : ∀ {y xs}
      → x ≤ y
      → x ≤-head y ∷ xs
  data sorted : list A → Set where
    [] : sorted []
    _∷_ : ∀ {x xs}
      → x ≤-head xs
      → sorted xs
      → sorted (x ∷ xs)

-- ==== --
-- Bags --
-- ==== --

-- operations --

module _ {A : Set} {{_ : has[<?] A}} where
  insertᴮ : A → list A → list A
  insertᴮ x [] = x ∷ []
  insertᴮ x (y ∷ ys) with x ≤? y
  … | LE = x ∷ y ∷ ys
  … | GT = y ∷ insertᴮ x ys
  
  _⊎ᴮ♮_ : list A → list A → list A
  [] ⊎ᴮ♮ ys = ys
  (x ∷ xs) ⊎ᴮ♮ ys = insertᴮ x (xs ⊎ᴮ♮ ys)

-- sorted --

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where 
  insertᴮ-≤-head : ∀ (x y : A) (xs : list A) → y ≤ x → y ≤-head xs → y ≤-head insertᴮ x xs
  insertᴮ-≤-head x y [] ε₁ [] = ⟨ ε₁ ⟩
  insertᴮ-≤-head x y (z ∷ xs) ε₁ ⟨ ε₂ ⟩ with x ≤? z
  … | LE = ⟨ ε₁ ⟩
  … | GT = ⟨ ε₂ ⟩

  insertᴮ-sorted : ∀ (x : A) (xs : list A) → sorted xs → sorted (insertᴮ x xs)
  insertᴮ-sorted x [] [] = [] ∷ []
  insertᴮ-sorted x (y ∷ xs) (ε ∷ εs) with x ≤? y | x ≤* y | x ≤~ y
  … | LE | LE ε′ | LE = ⟨ ε′ ⟩ ∷ ε ∷ εs
  … | GT | GT ε′ | GT = insertᴮ-≤-head x y xs (<-weaken y x ε′) ε ∷ insertᴮ-sorted x xs εs

  ⊎ᴮ♮-sorted : ∀ (xs ys : list A) → sorted ys → sorted (xs ⊎ᴮ♮ ys)
  ⊎ᴮ♮-sorted [] ys εs = εs
  ⊎ᴮ♮-sorted (x ∷ xs) ys εs = insertᴮ-sorted x (xs ⊎ᴮ♮ ys) (⊎ᴮ♮-sorted xs ys εs)

-- algebraic properties --

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where 
  insert-≤-head : ∀ (x : A) (xs : list A) → x ≤-head xs → insertᴮ x xs ≡ x ∷ xs
  insert-≤-head x [] [] = refl
  insert-≤-head x (y ∷ xs) ⟨ ε ⟩ rewrite ≤?≡LE x y ε = refl

  insert-commu : ∀ (x y : A) (xs : list A) → sorted xs → insertᴮ x (insertᴮ y xs) ≡ insertᴮ y (insertᴮ x xs)
  insert-commu x y [] [] with x ≤? y | x ≤* y | x ≤~ y | y ≤? x | y ≤* x | y ≤~ x
  … | LE | LE ε | LE | LE | LE ε′ | LE rewrite ≤-antisym x y ε ε′ = refl
  … | LE | LE ε | LE | GT | GT ε′ | GT = refl
  … | GT | GT ε | GT | LE | LE ε′ | LE = refl
  … | GT | GT ε | GT | GT | GT ε′ | GT = absurd (<-asym x y ε′ ε)
  insert-commu x y (z ∷ xs) (ε ∷ εs) with x ∇* y
  insert-commu x y (z ∷ xs) (ε ∷ εs) | EQ refl with x ≤* z
  … | LE ε″ rewrite ≤?≡LE x z ε″ | ≤?≡LE x x (≤-refl x) = refl
  … | GT ε″ rewrite ≤?≡GT x z ε″ | ≤?≡GT x z ε″ = refl
  insert-commu x y (z ∷ xs) (ε ∷ εs) | LT ε′ with y ≤* z
  … | LE ε″ rewrite ≤?≡LE y z ε″
                  | ≤?≡LE x y (<-weaken x y ε′)
                  | ≤?≡LE x z (≤-trans x y z (<-weaken x y ε′) ε″)
                  | ≤?≡GT y x ε′
                  | ≤?≡LE y z ε″
                  = refl
  … | GT ε″ rewrite ≤?≡GT y z ε″ with x ≤* z
  … | LE ε‴ rewrite ≤?≡LE x z ε‴ | ≤?≡GT y x ε′ | ≤?≡GT y z ε″ = refl
  … | GT ε‴ rewrite ≤?≡GT x z ε‴ | ≤?≡GT y z ε″ | insert-commu x y xs εs = refl
  insert-commu x y (z ∷ xs) (ε ∷ εs) | GT ε′ with x ≤* z
  … | LE ε″ rewrite ≤?≡LE x z ε″
                  | ≤?≡LE y z (≤-trans y x z (<-weaken y x ε′) ε″)
                  | ≤?≡LE y x (<-weaken y x ε′)
                  | ≤?≡GT x y ε′
                  | ≤?≡LE x z ε″
                  = refl
  … | GT ε″ rewrite ≤?≡GT x z ε″ with y ≤* z
  … | LE ε‴ rewrite ≤?≡LE y z ε‴ | ≤?≡GT x y ε′ | ≤?≡GT x z ε″ = refl
  … | GT ε‴ rewrite ≤?≡GT y z ε‴ | ≤?≡GT x z ε″ | insert-commu x y xs εs = refl

  ⊎ᴮ♮-runit : ∀ (xs : list A) → sorted xs → xs ⊎ᴮ♮ [] ≡ xs
  ⊎ᴮ♮-runit [] [] = refl
  ⊎ᴮ♮-runit (x ∷ xs) (ε ∷ εs) rewrite ⊎ᴮ♮-runit xs εs | insert-≤-head x xs ε = refl

  insert-⊎ᴮ♮-dist : ∀ (x : A) (xs ys : list A) → sorted xs → sorted ys → insertᴮ x (xs ⊎ᴮ♮ ys) ≡ insertᴮ x xs ⊎ᴮ♮ ys
  insert-⊎ᴮ♮-dist x [] ys _ _ = refl
  insert-⊎ᴮ♮-dist x (y ∷ xs) ys (ε₁ ∷ εs₁) εs₂ with x ≤? y
  … | LE = refl
  … | GT rewrite sym (insert-⊎ᴮ♮-dist x xs ys εs₁ εs₂) | insert-commu x y (xs ⊎ᴮ♮ ys) (⊎ᴮ♮-sorted xs ys εs₂) = refl

  ⊎ᴮ♮-assoc : ∀ (xs ys zs : list A) → sorted xs → sorted ys → sorted zs → xs ⊎ᴮ♮ (ys ⊎ᴮ♮ zs) ≡ (xs ⊎ᴮ♮ ys) ⊎ᴮ♮ zs
  ⊎ᴮ♮-assoc [] ys zs _ _ _ = refl
  ⊎ᴮ♮-assoc (x ∷ xs) ys zs (ε₁ ∷ εs₁) εs₂ εs₃
    rewrite ⊎ᴮ♮-assoc xs ys zs εs₁ εs₂ εs₃
          | insert-⊎ᴮ♮-dist x (xs ⊎ᴮ♮ ys) zs (⊎ᴮ♮-sorted xs ys εs₂) εs₃
          = refl

  ⊎ᴮ♮-rcons : ∀ (x : A) (xs ys : list A) → x ≤-head ys → sorted xs → sorted ys → xs ⊎ᴮ♮ (x ∷ ys) ≡ insertᴮ x (xs ⊎ᴮ♮ ys)
  ⊎ᴮ♮-rcons x [] ys ε₁ [] εs₃ rewrite insert-≤-head x ys ε₁ = refl
  ⊎ᴮ♮-rcons x (y ∷ xs) ys ε₁ (ε₂ ∷ εs₂) εs₃
    rewrite ⊎ᴮ♮-rcons x xs ys ε₁ εs₂ εs₃
          | insert-commu x y (xs ⊎ᴮ♮ ys) (⊎ᴮ♮-sorted xs ys εs₃)
          = refl

  ⊎ᴮ♮-commu : ∀ (xs ys : list A) → sorted xs → sorted ys → xs ⊎ᴮ♮ ys ≡ ys ⊎ᴮ♮ xs
  ⊎ᴮ♮-commu [] ys [] εs₂ rewrite ⊎ᴮ♮-runit ys εs₂ = refl
  ⊎ᴮ♮-commu (x ∷ xs) ys (ε₁ ∷ εs₁) εs₂ rewrite ⊎ᴮ♮-commu xs ys εs₁ εs₂ | ⊎ᴮ♮-rcons x ys xs ε₁ εs₂ εs₁ = refl

data bag (A : Set) {{_ : has[<] A}} : Set where
  ⟨_‣_⟩ : ∀ (xs : list A) → .(sorted xs) → bag A

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where
  bag-≡ : ∀ (xs ys : list A) (ε₁ : sorted xs) (ε₂ : sorted ys) → xs ≡ ys → ⟨ xs ‣ ε₁ ⟩ ≡ ⟨ ys ‣ ε₂ ⟩
  bag-≡ xs .xs _ _ refl = refl

  ∅ᴮ : {{_ : 𝟙}} → bag A
  ∅ᴮ {{TT}} = ⟨ [] ‣ [] ⟩

  b[_] : {{_ : 𝟙}} → A → bag A
  b[_] {{TT}} x = ⟨ [ x ] ‣ [] ∷ [] ⟩

  _⊎ᴮ_ : bag A → bag A → bag A
  ⟨ xs ‣ ε₁ ⟩ ⊎ᴮ ⟨ ys ‣ ε₂ ⟩ = ⟨ xs ⊎ᴮ♮ ys ‣ ⊎ᴮ♮-sorted xs ys ε₂ ⟩

  ⊎ᴮ-lunit : ∀ (xs : bag A) → ∅ᴮ ⊎ᴮ xs ≡ xs
  ⊎ᴮ-lunit ⟨ xs ‣ ε ⟩ rewrite unblock = refl

  ⊎ᴮ-runit : ∀ (xs : bag A) → xs ⊎ᴮ ∅ᴮ ≡ xs
  ⊎ᴮ-runit ⟨ xs ‣ ε ⟩ rewrite unblock = irr-≡ (bag-≡ (xs ⊎ᴮ♮ []) xs _ _ (⊎ᴮ♮-runit xs ε))

  ⊎ᴮ-assoc : ∀ (xs ys zs : bag A) → xs ⊎ᴮ (ys ⊎ᴮ zs) ≡ (xs ⊎ᴮ ys) ⊎ᴮ zs
  ⊎ᴮ-assoc ⟨ xs ‣ ε₁ ⟩ ⟨ ys ‣ ε₂ ⟩ ⟨ zs ‣ ε₃ ⟩ =
    irr-≡ (bag-≡ (xs ⊎ᴮ♮ (ys ⊎ᴮ♮ zs)) ((xs ⊎ᴮ♮ ys) ⊎ᴮ♮ zs)
                 (⊎ᴮ♮-sorted xs (ys ⊎ᴮ♮ zs) (⊎ᴮ♮-sorted ys zs ε₃))
                 (⊎ᴮ♮-sorted (xs ⊎ᴮ♮ ys) zs ε₃)
                 (⊎ᴮ♮-assoc xs ys zs ε₁ ε₂ ε₃))

  ⊎ᴮ-commu : ∀ (xs ys : bag A) → xs ⊎ᴮ ys ≡ ys ⊎ᴮ xs
  ⊎ᴮ-commu ⟨ xs ‣ ε₁ ⟩ ⟨ ys ‣ ε₂ ⟩ =
    irr-≡ (bag-≡ (xs ⊎ᴮ♮ ys)
                 (ys ⊎ᴮ♮ xs)
                 (⊎ᴮ♮-sorted xs ys ε₂)
                 (⊎ᴮ♮-sorted ys xs ε₁)
                 (⊎ᴮ♮-commu xs ys ε₁ ε₂))

  instance
    has[+][bag] : has[+] (bag A)
    has[+][bag] = record { zero = ∅ᴮ ; _+_ = _⊎ᴮ_ }

  instance
    cor[+][bag] : cor[+] (bag A)
    cor[+][bag] = record
      { +-lunit = ⊎ᴮ-lunit
      ; +-runit = ⊎ᴮ-runit
      ; +-assoc = ⊎ᴮ-assoc
      ; +-commu = ⊎ᴮ-commu
      }

{-# DISPLAY ∅ᴮ = zero #-}
{-# DISPLAY _⊎ᴮ_ = _+_ #-}

-- list elements --

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where
  list-elems : list A → bag A
  list-elems [] = zero
  list-elems (x ∷ xs) = b[ x ] + list-elems xs

-- ====================== --
-- Well Founded Relations --
-- ====================== --

data acc {A : Set} (_≺_ : A → A → Set) (x : A) : Set where
  Acc : (∀ {y} → y ≺ x → acc _≺_ y) → acc _≺_ x

irr-acc : ∀ {A : Set} {_≺_ : A → A → Set} {x : A} → .(acc _≺_ x) → acc _≺_ x
irr-acc (Acc r) = Acc λ ε → irr-acc (r ε)

record has[wf] {A : Set} (_≺_ : A → A → Set) : Set where
  field
    wf : ∀ x → acc _≺_ x
open has[wf] {{...}} public
    
{-# DISPLAY has[wf].wf _ = wf #-}

<ᴺ-wf′ : ∀ {m} (n : ℕ) → m < n → acc _<_ m
<ᴺ-wf′ Zero ()
<ᴺ-wf′ (Suc n) Zero = Acc λ where ()
<ᴺ-wf′ (Suc n) (Suc ε) = Acc λ where ε′ → (<ᴺ-wf′ n) (<-ltrans _ _ n (≤-fr-< ε′) ε)

<ᴺ-wf : ∀ (n : ℕ) → acc _<_ n
<ᴺ-wf n = Acc (<ᴺ-wf′ n)

instance
  has[wf][<ᴺ] : has[wf] _<ᴺ_
  has[wf][<ᴺ] = record { wf = <ᴺ-wf }

