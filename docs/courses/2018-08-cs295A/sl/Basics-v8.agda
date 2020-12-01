{-# OPTIONS --experimental-irrelevance #-}
module Basics-v8 where

infixl 0 AT-TYPE
infixr 1 CASE_OF_
infixr 1 _$_
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
  instance
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

_$_ : ∀ {A B : Set} → (A → B) → A → B
f $ x = f x

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

-- ------- --
-- monoids --
-- ------- --

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

-- ------------------- --
-- commutative monoids --
-- ------------------- --

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

-- ----- --
-- rings --
-- ----- --

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

[+] : ∀ {A : Set} {{_ : has[+] A}} → has[+] A
[+] {{X}} = X

c[+] : ∀ {A : Set} {{_ : has[+] A}} {{_ : cor[+] A}} → cor[+] A
c[+] {{_}} {{X}} = X

[*] : ∀ {A : Set} {{_ : has[+] A}} {{_ : has[*] A}} → has[+] A
[*] {{_}} {{_}} = record { zero = one ; _+_ = _*_ }

c[*] : ∀ {A : Set} {{_ : has[+] A}} {{_ : cor[+] A}} {{_ : has[*] A}} {{_ : cor[*] A}} → cor[+] A {{[*]}}
c[*] {{_}} {{_}} {{_}} {{X}} = record { +-lunit = *-lunit ; +-runit = *-runit ; +-assoc = *-assoc ; +-commu = *-commu }

{-# DISPLAY cor[*].*-lzero _ = *-lzero #-}
{-# DISPLAY cor[*].*-rzero _ = *-rzero #-}
{-# DISPLAY cor[*].*-lunit _ = *-lunit #-}
{-# DISPLAY cor[*].*-runit _ = *-runit #-}
{-# DISPLAY cor[*].*-assoc _ = *-assoc #-}
{-# DISPLAY cor[*].*-commu _ = *-commu #-}
{-# DISPLAY cor[*].*-ldist _ = *-ldist #-}
{-# DISPLAY cor[*].*-rdist _ = *-rdist #-}

-- ----------- --
-- total order --
-- ----------- --

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
    <-asym : ∀ (x y : A) → x < y → ¬ y ≤ x
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

-- deriving --

module _
  {A B : Set}
  {{_ : has[<] A}}
  {{_ : has[<] B}}
  {{_ : cor[<] B}}
  (ι : A → B)
  (inj[ι] : ∀ x y → ι x ≡ ι y → x ≡ y)
  (sound[<] : ∀ {x y} → x < y → ι x < ι y)
  (complete[<] : ∀ {x y} → ι x < ι y → x < y)
  (sound[≤] : ∀ {x y} → x ≤ y → ι x ≤ ι y)
  (complete[≤] : ∀ {x y} → ι x ≤ ι y → x ≤ y)
  where
  derive-≤-refl : ∀ (x : A) → x ≤ x
  derive-≤-refl x = complete[≤] (≤-refl (ι x))

  derive-≤-trans : ∀ (x y z : A) → x ≤ y → y ≤ z → x ≤ z
  derive-≤-trans x y z ε₁ ε₂ = complete[≤] (≤-trans (ι x) (ι y) (ι z) (sound[≤] ε₁) (sound[≤] ε₂))

  derive-≤-antisym : ∀ (x y : A) → x ≤ y → y ≤ x → x ≡ y
  derive-≤-antisym x y ε₁ ε₂ = inj[ι] x y (≤-antisym (ι x) (ι y) (sound[≤] ε₁) (sound[≤] ε₂))

  derive-<-irrefl : ∀ (x : A) → ¬ x < x
  derive-<-irrefl x ε = <-irrefl (ι x) (sound[<] ε)

  derive-<-trans : ∀ (x y z : A) → x < y → y < z → x < z
  derive-<-trans x y z ε₁ ε₂ = complete[<] (<-trans (ι x) (ι y) (ι z) (sound[<] ε₁) (sound[<] ε₂))

  derive-<-ltrans : ∀ (x y z : A) → x ≤ y → y < z → x < z
  derive-<-ltrans x y z ε₁ ε₂ = complete[<] (<-ltrans (ι x) (ι y) (ι z) (sound[≤] ε₁) (sound[<] ε₂))

  derive-<-rtrans : ∀ (x y z : A) → x < y → y ≤ z → x < z
  derive-<-rtrans x y z ε₁ ε₂ = complete[<] (<-rtrans (ι x) (ι y) (ι z) (sound[<] ε₁) (sound[≤] ε₂))

  derive-<-asym : ∀ (x y : A) → x < y → ¬ y ≤ x
  derive-<-asym x y ε ε′ = <-asym (ι x) (ι y) (sound[<] ε) (sound[≤] ε′)

  derive-<-weaken : ∀ (x y : A) → x < y → x ≤ y
  derive-<-weaken x y ε = complete[≤] (<-weaken (ι x) (ι y) (sound[<] ε))

  derive-<-splits : ∀ (x y : A) → x ≤ y → x < y ∨ x ≡ y
  derive-<-splits x y ε with <-splits (ι x) (ι y) (sound[≤] ε)
  … | Inl ε′ = Inl (complete[<] ε′)
  … | Inr ε′ = Inr (inj[ι] x y ε′)

  derive-cor[<] : cor[<] A
  derive-cor[<] = record
    { ≤-refl = derive-≤-refl
    ; ≤-trans = derive-≤-trans
    ; ≤-antisym = derive-≤-antisym
    ; <-irrefl = derive-<-irrefl
    ; <-trans = derive-<-trans
    ; <-ltrans = derive-<-ltrans
    ; <-rtrans = derive-<-rtrans
    ; <-asym = derive-<-asym
    ; <-weaken = derive-<-weaken
    ; <-splits = derive-<-splits
    }

-- ---------- --
-- comparison --
-- ---------- --

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
  … | Inl ε″ = absurd (<-asym x y ε″ (<-weaken y x ε′))
  … | Inr refl = absurd (<-irrefl x ε′)

  ≤?≡GT : ∀ (x y : A) → y < x → x ≤? y ≡ GT
  ≤?≡GT x y ε with x ≤? y | x ≤* y | x ≤~ y
  … | GT | GT _ | GT = refl
  … | LE | LE ε′ | LE with <-splits x y ε′
  … | Inl ε″ = absurd (<-asym x y ε″ (<-weaken y x ε))
  … | Inr refl = absurd (<-irrefl x ε)

-- deriving --

module _
  {A B : Set}
  {{_ : has[<] A}}
  {{_ : cor[<] A}}
  {{_ : has[<?] A}}
  {{_ : has[<] B}}
  {{_ : cor[<] B}}
  {{_ : has[<?] B}}
  {{_ : cor[<?] B}}
  (ι : A → B)
  (inj[ι] : ∀ x y → ι x ≡ ι y → x ≡ y)
  (complete[<] : ∀ {x y} → ι x < ι y → x < y)
  (complete[≤] : ∀ {x y} → ι x ≤ ι y → x ≤ y)
  (correct[≡?] : ∀ x y → ι x ≡? ι y ≡ x ≡? y)
  (correct[<?] : ∀ x y → ι x <? ι y ≡ x <? y)
  (correct[≤?] : ∀ x y → ι x ≤? ι y ≡ x ≤? y)
  (correct[∇?] : ∀ x y → ι x ∇? ι y ≡ x ∇? y)
  where

    derive-≡* : ∀ (x y : A) → ord[≡] x y
    derive-≡* x y with ι x ≡* ι y
    … | EQ ε = EQ (inj[ι] x y ε)
    … | NE ε = NE λ where refl → ε refl

    derive-≡~ : ∀ (x y : A) → link[≡] (x ≡? y) (derive-≡* x y)
    derive-≡~ x y with ι x ≡? ι y | ι x ≡* ι y | ι x ≡~ ι y | x ≡? y | derive-≡* x y | correct[≡?] x y
    derive-≡~ x y | EQ | EQ ε₁ | EQ | EQ | EQ ε₂ | refl = EQ
    derive-≡~ x y | EQ | EQ ε₁ | EQ | EQ | NE ε₂ | refl = absurd (ε₂ (inj[ι] x y ε₁))
    derive-≡~ x y | NE | NE ε₁ | NE | NE | EQ ε₂ | refl = CASE ε₂ OF λ where refl → absurd (ε₁ refl)
    derive-≡~ x y | NE | NE ε₁ | NE | NE | NE ε₂ | refl = NE

    derive-<* : ∀ (x y : A) → ord[<][ _≤_ , _<_ ] x y
    derive-<* x y with ι x <* ι y
    … | LT ε = LT (complete[<] ε)
    … | GE ε = GE (complete[≤] ε)

    derive-<~ : ∀ (x y : A) → link[<][ _≤_ , _<_ ] (x <? y) (derive-<* x y)
    derive-<~ x y with ι x <? ι y | ι x <* ι y | ι x <~ ι y | x <? y | derive-<* x y | correct[<?] x y
    derive-<~ x y | LT | LT ε₁ | LT | LT | LT ε₂ | refl = LT
    derive-<~ x y | LT | LT ε₁ | LT | LT | GE ε₂ | refl = absurd (<-asym x y (complete[<] ε₁) ε₂)
    derive-<~ x y | GE | GE ε₁ | GE | GE | LT ε₂ | refl = absurd (<-asym x y ε₂ (complete[≤] ε₁))
    derive-<~ x y | GE | GE ε₁ | GE | GE | GE ε₂ | refl = GE

    derive-≤* : ∀ (x y : A) → ord[≤][ _≤_ , _<_ ] x y
    derive-≤* x y with ι x ≤* ι y
    … | LE ε = LE (complete[≤] ε)
    … | GT ε = GT (complete[<] ε)

    derive-≤~ : ∀ (x y : A) → link[≤][ _≤_ , _<_ ] (x ≤? y) (derive-≤* x y)
    derive-≤~ x y with ι x ≤? ι y | ι x ≤* ι y | ι x ≤~ ι y | x ≤? y | derive-≤* x y | correct[≤?] x y
    derive-≤~ x y | LE | LE ε₁ | LE | LE | LE ε₂ | refl = LE
    derive-≤~ x y | LE | LE ε₁ | LE | LE | GT ε₂ | refl = absurd (<-asym y x ε₂ (complete[≤] ε₁))
    derive-≤~ x y | GT | GT ε₁ | GT | GT | LE ε₂ | refl = absurd (<-asym y x (complete[<] ε₁) ε₂)
    derive-≤~ x y | GT | GT ε₁ | GT | GT | GT ε₂ | refl = GT

    derive-∇* : ∀ (x y : A) → ord[∇][ _<_ ] x y
    derive-∇* x y with ι x ∇* ι y
    … | LT ε = LT (complete[<] ε)
    … | EQ ε = EQ (inj[ι] x y ε)
    … | GT ε = GT (complete[<] ε)

    derive-∇~ : ∀ (x y : A) → link[∇][ _<_ ] (x ∇? y) (derive-∇* x y)
    derive-∇~ x y with ι x ∇? ι y | ι x ∇* ι y | ι x ∇~ ι y | x ∇? y | derive-∇* x y | correct[∇?] x y
    derive-∇~ x y | LT | LT ε₁ | LT | LT | LT ε₂ | refl = LT
    derive-∇~ x y | LT | LT ε₁ | LT | LT | EQ ε₂ | refl rewrite ε₂ = absurd (<-irrefl (ι y) ε₁)
    derive-∇~ x y | LT | LT ε₁ | LT | LT | GT ε₂ | refl = absurd (<-asym x y (complete[<] ε₁) (<-weaken y x ε₂))
    derive-∇~ x y | EQ | EQ ε₁ | EQ | EQ | LT ε₂ | refl rewrite inj[ι] x y ε₁ = absurd (<-irrefl y ε₂)
    derive-∇~ x y | EQ | EQ ε₁ | EQ | EQ | EQ ε₂ | refl = EQ
    derive-∇~ x y | EQ | EQ ε₁ | EQ | EQ | GT ε₂ | refl rewrite inj[ι] x y ε₁ = absurd (<-irrefl y ε₂)
    derive-∇~ x y | GT | GT ε₁ | GT | GT | LT ε₂ | refl = absurd (<-asym x y ε₂ (<-weaken y x (complete[<] ε₁)))
    derive-∇~ x y | GT | GT ε₁ | GT | GT | EQ ε₂ | refl rewrite ε₂ = absurd (<-irrefl (ι y) ε₁)
    derive-∇~ x y | GT | GT ε₁ | GT | GT | GT ε₂ | refl = GT

    derive-cor[<?] : cor[<?] A
    derive-cor[<?] = record
      { _≡*_ = derive-≡*
      ; _≡~_ = derive-≡~
      ; _<*_ = derive-<*
      ; _<~_ = derive-<~
      ; _≤*_ = derive-≤*
      ; _≤~_ = derive-≤~
      ; _∇*_ = derive-∇*
      ; _∇~_ = derive-∇~
      }

-- ===== --
-- bools --
-- ===== --

data 𝔹 : Set where
  True : 𝔹
  False : 𝔹

{-# BUILTIN BOOL 𝔹 #-}
{-# BUILTIN TRUE True #-}
{-# BUILTIN FALSE False #-}

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

<ᴺ-splits : ∀ (m n : ℕ) → m ≤ n → m < n ∨ m ≡ n
<ᴺ-splits Zero Zero Zero = Inr refl
<ᴺ-splits Zero (Suc n) Zero = Inl Zero
<ᴺ-splits (Suc m) Zero ()
<ᴺ-splits (Suc m) (Suc n) (Suc ε) with <ᴺ-splits m n ε
… | Inl ε′ = Inl (Suc ε′)
… | Inr ε′ rewrite ε′ = Inr refl

<ᴺ-asym : ∀ (m n : ℕ) → m <ᴺ n → ¬ n ≤ᴺ m
<ᴺ-asym m n ε₁ ε₂ with <ᴺ-splits n m ε₂
… | Inl ε = <ᴺ-irrefl n (<ᴺ-trans _ _ _ ε ε₁)
… | Inr refl = <ᴺ-irrefl n ε₁

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

{-# BUILTIN LIST list #-}

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

-----------------
-- total order --
-----------------

module _ {A : Set} {{_ : has[<] A}} where
  data _<ᴸ_ : ∀ (xs ys : list A) → Set where
    [] : ∀ {x xs} → [] <ᴸ (x ∷ xs)
    [<] : ∀ {x y xs ys} → x < y → (x ∷ xs) <ᴸ (y ∷ ys)
    [≡] : ∀ {x y xs ys} → x ≡ y → xs <ᴸ ys → (x ∷ xs) <ᴸ (y ∷ ys)
  data _≤ᴸ_ : ∀ (xs ys : list A) → Set where
    [] : ∀ {xs} → [] ≤ᴸ xs
    [<] : ∀ {x y xs ys} → x < y → (x ∷ xs) ≤ᴸ (y ∷ ys)
    [≡] : ∀ {x y xs ys} → x ≡ y → xs ≤ᴸ ys → (x ∷ xs) ≤ᴸ (y ∷ ys)

instance
  has[<][list] : ∀ {A} {{_ : has[<] A}} → has[<] (list A)
  has[<][list] = record { _<_ = _<ᴸ_ ; _≤_ = _≤ᴸ_ }

postulate
  instance
    cor[<][list] : ∀ {A} {{_ : has[<] A}} {{_ : cor[<] A}} → cor[<] (list A)

module _ {A : Set} {{_ : has[<?] A}} where
  _∇?ᴸ_ : ∀ (xs ys : list A) → comp[∇]
  [] ∇?ᴸ [] = EQ
  [] ∇?ᴸ (y ∷ ys) = LT
  (x ∷ xs) ∇?ᴸ [] = GT
  (x ∷ xs) ∇?ᴸ (y ∷ ys) with x ∇? y
  … | LT = LT
  … | EQ = xs ∇?ᴸ ys
  … | GT = GT

  _≡?ᴸ_ : ∀ (xs ys : list A) → comp[≡]
  xs ≡?ᴸ ys with xs ∇?ᴸ ys
  … | LT = NE
  … | EQ = EQ
  … | GT = NE

  _<?ᴸ_ : ∀ (xs ys : list A) → comp[<]
  xs <?ᴸ ys with xs ∇?ᴸ ys
  … | LT = LT
  … | EQ = GE
  … | GT = GE

  _≤?ᴸ_ : ∀ (xs ys : list A) → comp[≤]
  xs ≤?ᴸ ys with xs ∇?ᴸ ys
  … | LT = LE
  … | EQ = LE
  … | GT = GT

instance
  has[<?][list] : ∀ {A} {{_ : has[<?] A}} → has[<?] (list A)
  has[<?][list] = record { _≡?_ = _≡?ᴸ_ ; _<?_ = _<?ᴸ_ ; _≤?_ = _≤?ᴸ_ ; _∇?_ = _∇?ᴸ_ }

postulate
  instance
    cor[<?][list] : ∀ {A} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} → cor[<?] (list A)

-- ======= --
-- vectors --
-- ======= --

syntax vec A n = vec[ n ] A
data vec (A : Set) : ℕ → Set where
  [] : vec[ 0 ] A
  _∷_ : ∀ {n} → A → vec[ n ] A → vec[ Suc n ] A

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

matrix[_,_] : ℕ → ℕ → Set → Set
matrix[ m , n ] A = vec[ m ] (vec[ n ] A)

graph : ℕ → Set
graph n = matrix[ n , n ] 𝔹

-- ===== --
-- index --
-- ===== --

data idx : ℕ → Set where
  Zero : ∀ {n} → idx (Suc n)
  Suc : ∀ {n} → idx n → idx (Suc n)

𝕚 : ∀ (n : ℕ) {m : ℕ} {{_ : n <? m ≡ LT}} → idx m
𝕚 Zero {Zero} ⦃ () ⦄
𝕚 Zero {Suc m} ⦃ ε ⦄ = Zero
𝕚 (Suc n) {Zero} ⦃ () ⦄
𝕚 (Suc n) {Suc m} ⦃ ε ⦄ = Suc (𝕚 n)

𝕟 : ∀ {n : ℕ} (i : idx n) → ℕ
𝕟 Zero = Zero
𝕟 (Suc i) = Suc (𝕟 i)

inj[𝕟] : ∀ {N} (x y : idx N) → 𝕟 x ≡ 𝕟 y → x ≡ y
inj[𝕟] Zero Zero ε = refl
inj[𝕟] Zero (Suc y) ()
inj[𝕟] (Suc x) Zero ()
inj[𝕟] (Suc x) (Suc y) ε with  𝕟 x | 𝕟 y | inj[𝕟] x y | ε
… | nx | .nx | rc | refl rewrite rc refl = refl

module _ {A : Set} where

  const[_] : ∀ n → A → vec[ n ] A
  const[ Zero ] x = []
  const[ Suc n ] x = x ∷ const[ n ] x

  _[[_]] : ∀ {n} → vec[ n ] A → idx n → A
  (x ∷ xs) [[ Zero ]] = x
  (x ∷ xs) [[ Suc ι ]] = xs [[ ι ]]

  _[[_↦_]] : ∀ {n} → vec[ n ] A → idx n → A → vec[ n ] A
  (x ∷ xs) [[ Zero ↦ x′ ]] = x′ ∷ xs
  (x ∷ xs) [[ Suc ι ↦ x′ ]] = x ∷ (xs [[ ι ↦ x′ ]])

  vec-iter : ∀ {B : Set} {n} → vec[ n ] A → B → (idx n → A → B → B) → B
  vec-iter [] i f = i
  vec-iter (x ∷ xs) i f = vec-iter xs (f Zero x i) λ ι x y → f (Suc ι) x y

-- ----------- --
-- total order --
-- ----------- --

data _<ᶥ_ : ∀ {N} → idx N → idx N → Set where
  Zero : ∀ {N} {ι : idx N} → Zero <ᶥ Suc ι
  Suc : ∀ {N} {ι₁ ι₂ : idx N} → ι₁ <ᶥ ι₂ → Suc ι₁ <ᶥ Suc ι₂

data _≤ᶥ_ : ∀ {N} → idx N → idx N → Set where
  Zero : ∀ {N} {ι : idx (Suc N)} → Zero ≤ᶥ ι
  Suc : ∀ {N} {ι₁ ι₂ : idx N} → ι₁ ≤ᶥ ι₂ → Suc ι₁ ≤ᶥ Suc ι₂

instance
  has[<][idx] : ∀ {N} → has[<] (idx N)
  has[<][idx] = record { _<_ = _<ᶥ_ ; _≤_ = _≤ᶥ_ }

sound[<ᶥ] : ∀ {N} {x y : idx N} → x < y → 𝕟 x < 𝕟 y
sound[<ᶥ] Zero = Zero
sound[<ᶥ] (Suc ε) = Suc (sound[<ᶥ] ε)

complete[<ᶥ] : ∀ {N} {x y : idx N} → 𝕟 x < 𝕟 y → x < y
complete[<ᶥ] {x = Zero} {Zero} ()
complete[<ᶥ] {x = Zero} {Suc y} Zero = Zero
complete[<ᶥ] {x = Suc x} {Zero} ()
complete[<ᶥ] {x = Suc x} {Suc y} (Suc ε) = Suc (complete[<ᶥ] ε)

sound[≤ᶥ] : ∀ {N} {x y : idx N} → x ≤ y → 𝕟 x ≤ 𝕟 y
sound[≤ᶥ] Zero = Zero
sound[≤ᶥ] (Suc ε) = Suc (sound[≤ᶥ] ε)

complete[≤ᶥ] : ∀ {N} {x y : idx N} → 𝕟 x ≤ 𝕟 y → x ≤ y
complete[≤ᶥ] {x = Zero} {y} Zero = Zero
complete[≤ᶥ] {x = Suc x} {Zero} ()
complete[≤ᶥ] {x = Suc x} {Suc y} (Suc ε) = Suc (complete[≤ᶥ] ε)

instance
  cor[<][idx] : ∀ {N} → cor[<] (idx N)
  cor[<][idx] = derive-cor[<] 𝕟 inj[𝕟] sound[<ᶥ] complete[<ᶥ] sound[≤ᶥ] complete[≤ᶥ]

-- ---------- --
-- comparison --
-- ---------- --

_≡?ᶥ_ : ∀ {N} (x y : idx N) → comp[≡]
Zero ≡?ᶥ Zero = EQ
Zero ≡?ᶥ Suc y = NE
Suc x ≡?ᶥ Zero = NE
Suc x ≡?ᶥ Suc y = x ≡?ᶥ y

_<?ᶥ_ : ∀ {N} (x y : idx N) → comp[<]
Zero <?ᶥ Zero = GE
Zero <?ᶥ Suc y = LT
Suc x <?ᶥ Zero = GE
Suc x <?ᶥ Suc y = x <?ᶥ y

_≤?ᶥ_ : ∀ {N} (x y : idx N) → comp[≤]
Zero ≤?ᶥ Zero = LE
Zero ≤?ᶥ Suc y = LE
Suc x ≤?ᶥ Zero = GT
Suc x ≤?ᶥ Suc y = x ≤?ᶥ y

_∇?ᶥ_ : ∀ {N} (x y : idx N) → comp[∇]
Zero ∇?ᶥ Zero = EQ
Zero ∇?ᶥ Suc y = LT
Suc x ∇?ᶥ Zero = GT
Suc x ∇?ᶥ Suc y = x ∇?ᶥ y

instance
  has[<?][idx] : ∀ {N} → has[<?] (idx N)
  has[<?][idx] = record { _≡?_ = _≡?ᶥ_ ; _<?_ = _<?ᶥ_ ; _≤?_ = _≤?ᶥ_ ; _∇?_ = _∇?ᶥ_ }

correct[≡?] : ∀ {N} (x y : idx N) → 𝕟 x ≡? 𝕟 y ≡ x ≡? y
correct[≡?] Zero Zero = refl
correct[≡?] Zero (Suc y) = refl
correct[≡?] (Suc x) Zero = refl
correct[≡?] (Suc x) (Suc y) = correct[≡?] x y

correct[<?] : ∀ {N} (x y : idx N) → 𝕟 x <? 𝕟 y ≡ x <? y
correct[<?] Zero Zero = refl
correct[<?] Zero (Suc y) = refl
correct[<?] (Suc x) Zero = refl
correct[<?] (Suc x) (Suc y) = correct[<?] x y

correct[≤?] : ∀ {N} (x y : idx N) → 𝕟 x ≤? 𝕟 y ≡ x ≤? y
correct[≤?] Zero Zero = refl
correct[≤?] Zero (Suc y) = refl
correct[≤?] (Suc x) Zero = refl
correct[≤?] (Suc x) (Suc y) = correct[≤?] x y

correct[∇?] : ∀ {N} (x y : idx N) → 𝕟 x ∇? 𝕟 y ≡ x ∇? y
correct[∇?] Zero Zero = refl
correct[∇?] Zero (Suc y) = refl
correct[∇?] (Suc x) Zero = refl
correct[∇?] (Suc x) (Suc y) = correct[∇?] x y

instance
  cor[<?][idx] : ∀ {N} → cor[<?] (idx N)
  cor[<?][idx] = derive-cor[<?] 𝕟 inj[𝕟] complete[<ᶥ] complete[≤ᶥ] correct[≡?] correct[<?] correct[≤?] correct[∇?]

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

-- -------------- --
-- raw operations --
-- -------------- --

module _ {A : Set} {{_ : has[<?] A}} where
  insertᴮ : A → list A → list A
  insertᴮ x [] = x ∷ []
  insertᴮ x (y ∷ ys) with x ≤? y
  … | LE = x ∷ y ∷ ys
  … | GT = y ∷ insertᴮ x ys
  
  _⊎ᴮ♮_ : list A → list A → list A
  [] ⊎ᴮ♮ ys = ys
  (x ∷ xs) ⊎ᴮ♮ ys = insertᴮ x (xs ⊎ᴮ♮ ys)

  _⨳ᴮ♮_ : ∀ {{_ : has[+] A}} → list A → list A → list A
  [] ⨳ᴮ♮ y = []
  (x ∷ xs) ⨳ᴮ♮ ys = map (λ y → x + y) ys ⊎ᴮ♮ (xs ⨳ᴮ♮ ys)

-- ------ --
-- sorted --
-- ------ --

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

-- ------- --
-- algebra --
-- ------- --

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where 
  insert-≤-head : ∀ (x : A) (xs : list A) → x ≤-head xs → insertᴮ x xs ≡ x ∷ xs
  insert-≤-head x [] [] = refl
  insert-≤-head x (y ∷ xs) ⟨ ε ⟩ rewrite ≤?≡LE x y ε = refl

  insert-commu : ∀ (x y : A) (xs : list A) → sorted xs → insertᴮ x (insertᴮ y xs) ≡ insertᴮ y (insertᴮ x xs)
  insert-commu x y [] [] with x ≤? y | x ≤* y | x ≤~ y | y ≤? x | y ≤* x | y ≤~ x
  … | LE | LE ε | LE | LE | LE ε′ | LE rewrite ≤-antisym x y ε ε′ = refl
  … | LE | LE ε | LE | GT | GT ε′ | GT = refl
  … | GT | GT ε | GT | LE | LE ε′ | LE = refl
  … | GT | GT ε | GT | GT | GT ε′ | GT = absurd (<-asym x y ε′ (<-weaken y x ε))
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

-- --------- --
-- container --
-- --------- --

data bag (A : Set) {{_ : has[<] A}} : Set where
  ⟨_‣_⟩ : ∀ (xs : list A) → .(sorted xs) → bag A

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where
  bag-≡ : ∀ (xs ys : list A) (ε₁ : sorted xs) (ε₂ : sorted ys) → xs ≡ ys → ⟨ xs ‣ ε₁ ⟩ ≡ ⟨ ys ‣ ε₂ ⟩
  bag-≡ xs .xs _ _ refl = refl

  ∅♭ᴮ : bag A
  ∅♭ᴮ = ⟨ [] ‣ [] ⟩

  ∅ᴮ : {{_ : 𝟙}} → bag A
  ∅ᴮ {{TT}} = ∅♭ᴮ

  b♭[_] : A → bag A
  b♭[ x ] = ⟨ [ x ] ‣ [] ∷ [] ⟩

  b[_] : {{_ : 𝟙}} → A → bag A
  b[_] {{TT}} = b♭[_]

  _⊎ᴮ_ : bag A → bag A → bag A
  ⟨ xs ‣ ε₁ ⟩ ⊎ᴮ ⟨ ys ‣ ε₂ ⟩ = ⟨ xs ⊎ᴮ♮ ys ‣ ⊎ᴮ♮-sorted xs ys ε₂ ⟩

  _⨳ᴮ_ : ∀ {{_ : has[+] A}} → bag A → bag A → bag A
  ⟨ xs ‣ ε₁ ⟩ ⨳ᴮ ⟨ ys ‣ ε₂ ⟩ = ⟨ xs ⨳ᴮ♮ ys ‣ TRUSTME ⟩
    where
      postulate
        TRUSTME : sorted (xs ⨳ᴮ♮ ys)

  ⊎ᴮ-lunit : ∀ (xs : bag A) → ∅♭ᴮ ⊎ᴮ xs ≡ xs
  ⊎ᴮ-lunit ⟨ xs ‣ ε ⟩ = refl

  ⊎ᴮ-runit : ∀ (xs : bag A) → xs ⊎ᴮ ∅♭ᴮ ≡ xs
  ⊎ᴮ-runit ⟨ xs ‣ ε ⟩ = irr-≡ (bag-≡ (xs ⊎ᴮ♮ []) xs _ _ (⊎ᴮ♮-runit xs ε))

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

  -- instance
  --   has[+][bag] : has[+] (bag A)
  --   has[+][bag] = record { zero = ∅ᴮ ; _+_ = _⊎ᴮ_ }

  instance
    has[+][bag] : has[+] (bag A)
    has[+][bag] = record { zero = ∅♭ᴮ ; _+_ = _⊎ᴮ_ }

  instance
    cor[+][bag] : cor[+] (bag A)
    cor[+][bag] = record
      { +-lunit = ⊎ᴮ-lunit
      ; +-runit = ⊎ᴮ-runit
      ; +-assoc = ⊎ᴮ-assoc
      ; +-commu = ⊎ᴮ-commu
      }

  -- instance
  --   has[*][bag] : ∀ {{_ : has[+] A}} → has[*] (bag A)
  --   has[*][bag] = record { one = b[ zero ] ; _*_ = _⨳ᴮ_ }

  instance
    has[*][bag] : ∀ {{_ : has[+] A}} → has[*] (bag A)
    has[*][bag] = record { one = b♭[ zero ] ; _*_ = _⨳ᴮ_ }

  postulate
    instance
      cor[*][bag] : ∀ {{_ : has[+] A}} {{_ : cor[+] A}} → cor[*] (bag A)

{-# DISPLAY ∅ᴮ = zero #-}
{-# DISPLAY _⊎ᴮ_ = _+_ #-}

-- list elements --

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where
  𝕓 : list A → bag A
  𝕓 [] = zero
  𝕓 (x ∷ xs) = b[ x ] + 𝕓 xs

-- bag fold --

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where
  module _ {B : Set} (M : has[+] B) where
    private
      instance
        _ = M

    reduce : bag A → (A → B) → B
    reduce ⟨ [] ‣ ε ⟩ f = zero
    reduce ⟨ x ∷ xs ‣ _ ∷ εs ⟩ f = f x + reduce ⟨ xs ‣ εs ⟩ f

    reduce-zero : (f : A → B) → reduce zero f ≡ zero
    reduce-zero f rewrite unblock = refl

  module _ {B : Set} (M₁ : has[+] B) (M₂ : cor[+] B {{M₁}}) where
    private
      instance
        _ = M₁
        _ = M₂

    postulate
      reduce-cons : (x : A) (xs : bag A) (f : A → B) → reduce M₁ (b[ x ] + xs) f ≡ f x + reduce M₁ xs f
  
-- --------- --
-- injection --
-- --------- --

module _ {A : Set} {{_ : has[<] A}} where
  𝕝 : bag A → list A
  𝕝 ⟨ xs ‣ ε ⟩ = xs

  data _<ᴮ_ : bag A → bag A → Set where
    ⟨_⟩ : ∀ {xs ys : bag A} → 𝕝 xs < 𝕝 ys → xs <ᴮ ys

  data _≤ᴮ_ : bag A → bag A → Set where
    ⟨_⟩ : ∀ {xs ys : bag A} → 𝕝 xs ≤ 𝕝 ys → xs ≤ᴮ ys

  instance
    has[<][bag] : has[<] (bag A)
    has[<][bag] = record { _<_ = _<ᴮ_ ; _≤_ = _≤ᴮ_ }

  postulate
    instance
      cor[<][bag] : ∀ {{_ : cor[<] A}} → cor[<] (bag A)

  module _ {{_ : has[<?] A}} where
    _≡?ᴮ_ : ∀ (xs ys : bag A) → comp[≡]
    ⟨ xs ‣ _ ⟩ ≡?ᴮ ⟨ ys ‣ _ ⟩ = xs ≡? ys 

    _<?ᴮ_ : ∀ (xs ys : bag A) → comp[<]
    ⟨ xs ‣ _ ⟩ <?ᴮ ⟨ ys ‣ _ ⟩ = xs <? ys 

    _≤?ᴮ_ : ∀ (xs ys : bag A) → comp[≤]
    ⟨ xs ‣ _ ⟩ ≤?ᴮ ⟨ ys ‣ _ ⟩ = xs ≤? ys 

    _∇?ᴮ_ : ∀ (xs ys : bag A) → comp[∇]
    ⟨ xs ‣ _ ⟩ ∇?ᴮ ⟨ ys ‣ _ ⟩ = xs ∇? ys 

    instance
      has[<?][bag] : has[<?] (bag A)
      has[<?][bag] = record { _≡?_ = _≡?ᴮ_ ; _<?_ = _<?ᴮ_ ; _≤?_ = _≤?ᴮ_ ; _∇?_ = _∇?ᴮ_ }

    postulate
      instance
        cor[<?][bag] : ∀ {{_ : cor[<] A}} {{_ : cor[<?] A}} → cor[<?] (bag A)

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

-- ======== --
-- Remember --
-- ======== --

delay : Set → Set
delay A = 𝟙 → A

hide : ∀ {A : Set} {B : A → Set} (f : ∀ (x : A) → B x) (x : A) → delay (B x)
hide f x TT = f x

reveal : ∀ {A : Set} → delay A → A
reveal x = x TT

data recall_𝑖𝑠_ {A : Set} (x : A) (y : delay A) : Set where
 Was : reveal y ≡ x → recall x 𝑖𝑠 y

remember : ∀ {A : Set} {B : Set} (f : A → B) (x : A) → recall f x 𝑖𝑠 hide f x
remember f x = Was refl

-- ========== --
-- Characters --
-- ========== --

postulate ℂ : Set
{-# BUILTIN CHAR ℂ #-}

module ℂ-prim where
  primitive
    primIsLower      : ℂ → 𝔹
    primIsDigit      : ℂ → 𝔹
    primIsAlpha      : ℂ → 𝔹
    primIsSpace      : ℂ → 𝔹
    primIsAscii      : ℂ → 𝔹
    primIsLatin1     : ℂ → 𝔹
    primIsPrint      : ℂ → 𝔹
    primIsHexDigit   : ℂ → 𝔹
    primToUpper      : ℂ → ℂ
    primToLower      : ℂ → ℂ
    primCharToNat    : ℂ → ℕ
    primNatToChar    : ℕ → ℂ
    primCharEquality : ℂ → ℂ → 𝔹
open ℂ-prim public renaming
  ( primIsLower      to ℂis-lower
  ; primIsDigit      to ℂis-digit
  ; primIsAlpha      to ℂis-alpha
  ; primIsSpace      to ℂis-space
  ; primIsAscii      to ℂis-ascii
  ; primIsLatin1     to ℂis-latin1
  ; primIsPrint      to ℂis-print
  ; primIsHexDigit   to ℂis-hex-digit
  ; primToUpper      to ℂto-upper
  ; primToLower      to ℂto-lower
  ; primCharToNat    to ℕℂ
  ; primNatToChar    to ℂℕ
  ; primCharEquality to _ℂ≡?_
  )

-- ======= --
-- Strings --
-- ======= --

postulate 𝕊 : Set
{-# BUILTIN STRING 𝕊 #-}

module 𝕊-prim where
  primitive
    primStringToList   : 𝕊 → list ℂ
    primStringFromList : list ℂ → 𝕊
    primStringAppend   : 𝕊 → 𝕊 → 𝕊
    primStringEquality : 𝕊 → 𝕊 → 𝔹
    primShowChar       : ℂ → 𝕊
    primShowString     : 𝕊 → 𝕊
open 𝕊-prim public renaming
  ( primStringToList   to list𝕊
  ; primStringFromList to 𝕊list
  ; primStringAppend   to _𝕊++_
  ; primStringEquality to _𝕊≡?_
  ; primShowChar       to ℂshow
  ; primShowString     to 𝕊show
  )

-- ======== --
-- Integers --
-- ======== --

data ℤ : Set where
  Pos : ℕ → ℤ
  NegSuc : ℕ → ℤ

{-# BUILTIN INTEGER ℤ #-}
{-# BUILTIN INTEGERPOS Pos #-}
{-# BUILTIN INTEGERNEGSUC NegSuc #-}

data _<ᶻ_ : ℤ → ℤ → Set where
  Pos<Pos : ∀ {x y} → x < y → Pos x <ᶻ Pos y
  NegS<Pos : ∀ {x y} → NegSuc x <ᶻ Pos y
  NegS<NegS : ∀ {x y} → y < x → NegSuc x <ᶻ NegSuc y

data _≤ᶻ_ : ℤ → ℤ → Set where
  Pos≤Pos : ∀ {x y} → x ≤ y → Pos x ≤ᶻ Pos y
  NegS≤Pos : ∀ {x y} → NegSuc x ≤ᶻ Pos y
  NegS≤NegS : ∀ {x y} → y ≤ x → NegSuc x ≤ᶻ NegSuc y

instance
  has[<][ℤ] : has[<] ℤ
  has[<][ℤ] = record { _<_ = _<ᶻ_ ; _≤_ = _≤ᶻ_ }

postulate
  instance
    cor[<][ℤ] : cor[<] ℤ

_≡?ᶻ_ : ∀ (x y : ℤ) → comp[≡]
Pos x ≡?ᶻ Pos y = x ≡? y
Pos x ≡?ᶻ NegSuc y = NE
NegSuc x ≡?ᶻ Pos y = NE
NegSuc x ≡?ᶻ NegSuc y = x ≡? y

_<?ᶻ_ : ∀ (x y : ℤ) → comp[<]
Pos x <?ᶻ Pos y = x <? y
Pos x <?ᶻ NegSuc y = GE
NegSuc x <?ᶻ Pos y = LT
NegSuc x <?ᶻ NegSuc y = y <? x

_≤?ᶻ_ : ∀ (x y : ℤ) → comp[≤]
Pos x ≤?ᶻ Pos y = x ≤? y
Pos x ≤?ᶻ NegSuc y = GT
NegSuc x ≤?ᶻ Pos y = LE
NegSuc x ≤?ᶻ NegSuc y = y ≤? x

_∇?ᶻ_ : ∀ (x y : ℤ) → comp[∇]
Pos x ∇?ᶻ Pos y = x ∇? y
Pos x ∇?ᶻ NegSuc y = GT
NegSuc x ∇?ᶻ Pos y = LT
NegSuc x ∇?ᶻ NegSuc y = y ∇? x

instance
  has[<?][ℤ] : has[<?] ℤ
  has[<?][ℤ] = record { _≡?_ = _≡?ᶻ_ ; _<?_ = _<?ᶻ_ ; _≤?_ = _≤?ᶻ_ ; _∇?_ = _∇?ᶻ_ }

postulate
  instance
    cor[<?][ℤ] : cor[<?] ℤ

_-ᴺ_ : ∀ (x y : ℕ) → ℤ
x -ᴺ Zero = Pos x
Zero -ᴺ Suc y = NegSuc y
Suc x -ᴺ Suc y = x -ᴺ y

_+ᶻ_ : ∀ (x y : ℤ) → ℤ
Pos x +ᶻ Pos y = Pos (x + y)
Pos x +ᶻ NegSuc y = x -ᴺ Suc y
NegSuc x +ᶻ Pos y = y -ᴺ Suc x
NegSuc x +ᶻ NegSuc y = NegSuc (Suc (x + y))

instance
  has[+][ℤ] : has[+] ℤ
  has[+][ℤ] = record { zero = Pos 0 ; _+_ = _+ᶻ_ }

postulate
  instance
    cor[+][ℤ] : cor[+] ℤ

_-ᶻ_ : ∀ (x y : ℤ) → ℤ
Pos x -ᶻ Pos y = x -ᴺ y
Pos x -ᶻ NegSuc y = Pos (Suc (x + y))
NegSuc x -ᶻ Pos y = NegSuc (x + y)
NegSuc x -ᶻ NegSuc y = y -ᴺ x

postulate
  inv[-ᶻ] : ∀ x y → x + (y -ᶻ x) ≡ y

_*ᶻ_ : ∀ (x y : ℤ) → ℤ
Pos x *ᶻ Pos y = Pos (x * y)
Pos Zero *ᶻ NegSuc y = Pos Zero
Pos (Suc x) *ᶻ NegSuc y = NegSuc (x * y + (x + y))
NegSuc x *ᶻ Pos Zero = Pos Zero
NegSuc x *ᶻ Pos (Suc y) = NegSuc (y * x + (y + x))
NegSuc x *ᶻ NegSuc y = Pos (Suc x * Suc y)

instance
  has[*][ℤ] : has[*] ℤ
  has[*][ℤ] = record { one = Pos 1 ; _*_ = _*ᶻ_ }

postulate
  instance
    cor[*][ℤ] : cor[*] ℤ

module ℤ-prim where
  primitive
    primShowInteger : ℤ → 𝕊
open ℤ-prim public renaming
  ( primShowInteger to ℤshow
  )

-- ====== --
-- Floats --
-- ====== --

postulate 𝔽 : Set
{-# BUILTIN FLOAT 𝔽 #-}

module 𝔽-prim where
  primitive
    primFloatEquality          : 𝔽 → 𝔽 → 𝔹
    primFloatLess              : 𝔽 → 𝔽 → 𝔹
    primFloatNumericalEquality : 𝔽 → 𝔽 → 𝔹
    primFloatNumericalLess     : 𝔽 → 𝔽 → 𝔹
    primNatToFloat             : ℕ → 𝔽
    primFloatPlus              : 𝔽 → 𝔽 → 𝔽
    primFloatMinus             : 𝔽 → 𝔽 → 𝔽
    primFloatTimes             : 𝔽 → 𝔽 → 𝔽
    primFloatNegate            : 𝔽 → 𝔽
    primFloatDiv               : 𝔽 → 𝔽 → 𝔽
    primFloatSqrt              : 𝔽 → 𝔽
    primRound                  : 𝔽 → ℤ
    primFloor                  : 𝔽 → ℤ
    primCeiling                : 𝔽 → ℤ
    primExp                    : 𝔽 → 𝔽
    primLog                    : 𝔽 → 𝔽
    primSin                    : 𝔽 → 𝔽
    primCos                    : 𝔽 → 𝔽
    primTan                    : 𝔽 → 𝔽
    primASin                   : 𝔽 → 𝔽
    primACos                   : 𝔽 → 𝔽
    primATan                   : 𝔽 → 𝔽
    primATan2                  : 𝔽 → 𝔽 → 𝔽
    primShowFloat              : 𝔽 → 𝕊
open 𝔽-prim public renaming
  ( primFloatEquality          to _𝔽≡?_
  ; primFloatLess              to _𝔽<?_
  ; primFloatNumericalEquality to _𝔽≈?_
  ; primFloatNumericalLess     to _𝔽≺?_
  ; primNatToFloat             to 𝔽ℕ
  ; primFloatPlus              to _𝔽+_
  ; primFloatMinus             to _𝔽-_
  ; primFloatTimes             to _𝔽×_
  ; primFloatNegate            to 𝔽⁻
  ; primFloatDiv               to _𝔽/_
  ; primFloatSqrt              to 𝔽√
  ; primRound                  to 𝔽round
  ; primFloor                  to 𝔽⌊_⌋
  ; primCeiling                to 𝔽⌈_⌉
  ; primExp                    to 𝔽e^
  ; primLog                    to 𝔽㏑
  ; primSin                    to 𝔽sin
  ; primCos                    to 𝔽cos
  ; primTan                    to 𝔽tan
  ; primASin                   to 𝔽asin
  ; primACos                   to 𝔽acos
  ; primATan                   to 𝔽atan
  ; primATan2                  to 𝔽atan2
  ; primShowFloat              to 𝔽show
  )

-- -- why doubles can be problematic...
-- _ : (1.0 𝔽/ 9.0) 𝔽× 9.0 ≡ 1.0
-- _ = {!!}

-- _ : (𝔽√ 2.0) 𝔽× (𝔽√ 2.0) ≡ 2.0
-- _ = {!!}

-- _ : ((1.0 𝔽/ 0.0) 𝔽≈? (1.0 𝔽/ 0.0)) ≡ {!!}
-- _ = {!!}
-- 
-- _ : ((1.0 𝔽/ 0.0) 𝔽≡? (1.0 𝔽/ 0.0)) ≡ {!!}
-- _ = {!!}
-- 
-- _ : ((0.0 𝔽/ 0.0) 𝔽≈? (0.0 𝔽/ 0.0)) ≡ {!!}
-- _ = {!!}

-- _ : ((0.0 𝔽/ 0.0) 𝔽≡? (0.0 𝔽/ 0.0)) ≡ {!!}
-- _ = {!!}
