-- [Much of this material is borrowed from [sf.vfa.Sort]
-- authored by Andrew Appel.]
-- 
-- [sf.vfa.Sort]: https://plfa.github.io/Lists/

module la11 where

---------
-- LIB --
---------

infix  4 ∃
infixl 5 _⊎_
infixl 6 _×_
infix  9 ¬_
infix  10 _≡_ _≤ᴺ_ _<ᴺ_
infix  14 _∇ᴺ_ _∇?ᴺ_ _∇!ᴺ_
infixl 15 _+ᴺ_ _∸ᴺ_ _++ᴸ_
infixl 16 _*ᴺ_
infixl 30 _∘_
infixr 20 _∷_

-- equality --

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- natural numbers --

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

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

-- ordering --

data _≤ᴺ_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ} → zero ≤ᴺ n
  suc : ∀ {m n : ℕ} → m ≤ᴺ n → suc m ≤ᴺ suc n

data _<ᴺ_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ} → zero <ᴺ suc n
  suc : ∀ {m n : ℕ} → m <ᴺ n → suc m <ᴺ suc n

data Comparison : Set where
  LT : Comparison
  EQ : Comparison
  GT : Comparison

_∇ᴺ_ : ℕ → ℕ → Comparison
zero ∇ᴺ zero = EQ
zero ∇ᴺ suc n = LT
suc m ∇ᴺ zero = GT
suc m ∇ᴺ suc n = m ∇ᴺ n

data Orderingᴺ (m n : ℕ) : Set where
  LT : m <ᴺ n → Orderingᴺ m n
  EQ : m ≡ n → Orderingᴺ m n
  GT : n <ᴺ m → Orderingᴺ m n

_∇?ᴺ_ : ∀ (m n : ℕ) → Orderingᴺ m n
zero ∇?ᴺ zero = EQ refl
zero ∇?ᴺ suc n = LT zero
suc m ∇?ᴺ zero = GT zero
suc m ∇?ᴺ suc n with m ∇?ᴺ n
… | LT ε = LT (suc ε)
… | EQ ε rewrite ε = EQ refl
… | GT ε = GT (suc ε)

data Linkᴺ {m n : ℕ} : Comparison → Orderingᴺ m n → Set where
  LT : ∀ {ε : m <ᴺ n} → Linkᴺ LT (LT ε)
  EQ : ∀ {ε : m ≡ n} → Linkᴺ EQ (EQ ε)
  GT : ∀ {ε : n <ᴺ m} → Linkᴺ GT (GT ε)

_∇!ᴺ_ : ∀ (m n : ℕ) → Linkᴺ (m ∇ᴺ n) (m ∇?ᴺ n)
zero ∇!ᴺ zero = EQ
zero ∇!ᴺ suc n = LT
suc m ∇!ᴺ zero = GT
suc m ∇!ᴺ suc n with m ∇ᴺ n | m ∇?ᴺ n | m ∇!ᴺ n
… | LT | LT ε | LT = LT
… | EQ | EQ ε | EQ rewrite ε = EQ
… | GT | GT ε | GT = GT

-- true, false, sums, products --

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data _⊎_ : Set → Set → Set where
  inj₁ : ∀ {A B : Set} → A → A ⊎ B
  inj₂ : ∀ {A B : Set} → B → A ⊎ B

data _×_ : Set → Set → Set where
  ⟨_,_⟩ : ∀ {A B : Set}
    → A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

-- existential types --

syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B
data ∃ (A : Set) (B : A → Set) : Set where
  ⟨∃_,_⟩ : (x : A) → B x → ∃ A B

-- function composition --

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- lists --

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

_++ᴸ_ : ∀ {A : Set} → List A → List A → List A
[] ++ᴸ ys = ys
(x ∷ xs) ++ᴸ ys = x ∷ (xs ++ᴸ ys)

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

--------------
-- IN CLASS --
--------------

record has[++] (A : Set) : Set where
  infixl 15 _++_
  field
    nil : A
    _++_ : A → A → A
open has[++] {{...}} public

instance
  has[++][List] : ∀ {A : Set} → has[++] (List A)
  has[++][List] = record { nil = [] ; _++_ = _++ᴸ_ }

  has[++][ℕ] : has[++] ℕ
  has[++][ℕ] = record { nil = 0 ; _++_ = _+ᴺ_ }

_ : [ 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 1 , 2 , 3 , 4 ]
_  = refl

_ : [ 1 , 2 ] ++ᴸ [ 3 , 4 ] ≡ [ 1 , 2 , 3 , 4 ]
_  = refl

_ : 2 ++ 4 ≡ 6
_  = refl

_ : 2 +ᴺ 4 ≡ 6
_  = refl

record cor[++] (A : Set) {{_ : has[++] A}} : Set where
  field
    ++-lunit : ∀ (x : A) → nil ++ x ≡ x
    ++-runit : ∀ (x : A) → x ++ nil ≡ x
    ++-assoc : ∀ (x y z : A) → x ++ (y ++ z) ≡ x ++ y ++ z
open cor[++] {{...}} public

postulate
  instance
    cor[++][List] : ∀ {A : Set} → cor[++] (List A)
    cor[++][ℕ] : cor[++] ℕ

_ : ∀ {A : Set} (xs : List A) → xs ++ nil ≡ xs
_ = ++-runit

_ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
_ = ++-runit

_ : ∀ {A : Set} (xs : List A) → xs ++ᴸ [] ≡ xs
_ = ++-runit

_ : ∀ (x : ℕ) → x ++ nil ≡ x
_ = ++-runit

_ : ∀ (x : ℕ) → x ++ 0 ≡ x
_ = ++-runit

_ : ∀ (x : ℕ) → x +ᴺ 0 ≡ x
_ = ++-runit

record has[+] (A : Set) : Set where
  infixl 15 _+_
  field
    none : A
    _+_ : A → A → A
open has[+] {{...}} public

instance
  has[+][ℕ] : has[+] ℕ
  has[+][ℕ] = record { none = 0 ; _+_ = _+ᴺ_ }

_ : 1 + 2 ≡ 3 + none
_ = refl

record cor[+] (A : Set) {{_ : has[+] A}} : Set where
  field
    +-lunit : ∀ (x : A) → none + x ≡ x
    +-runit : ∀ (x  : A) → x + none ≡ x
    +-assoc : ∀ (x y z : A) → x + (y + z) ≡ x + y + z
    +-commu : ∀ (x y : A) → x + y ≡ y + x
open cor[+] {{...}} public

postulate
  instance
    cor[+][ℕ] : cor[+] ℕ

_ : ∀ (m n : ℕ) → m + n ≡ n + m
_ = +-commu

record has[*] (A : Set) {{_ : has[+] A}} : Set where
  infixl 16 _*_
  field
    one : A
    _*_ : A → A → A
open has[*] {{...}} public

instance
  has[*][ℕ] : has[*] ℕ
  has[*][ℕ] = record { one = 1 ; _*_ = _*ᴺ_}

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

postulate
  instance
    cor[*][ℕ] : cor[*] ℕ

_ : ∀ (m : ℕ) → m * zero ≡ zero
_ = *-rzero

record has[<] (A : Set) : Set₁ where
  infix 10 _≤_
  infix 10 _<_
  field
    _<_ : A → A → Set
    _≤_ : A → A → Set
open has[<] {{...}} public

instance
  has[<][ℕ] : has[<] ℕ
  has[<][ℕ] = record { _<_ = _<ᴺ_ ; _≤_ = _≤ᴺ_ }

record cor[<] (A : Set) {{_ : has[<] A}} : Set₁ where
  field
    ≤-refl : ∀ (x : A) → x ≤ x
    ≤-trans : ∀ (x y z : A) → y ≤ z → x ≤ y → x ≤ z
    ≤-antisym : ∀ (x y : A) → x ≤ y → y ≤ x → x ≡ y
    <-irrefl : ∀ (x : A) → ¬ x < x
    <-trans : ∀ (x y z : A) → y < z → x < y → x < z
    <-asym : ∀ (x y : A) → ¬ (x < y × y < x)
    <-weaken : ∀ (x y : A) → x < y → x ≤ y
    <-invert : ∀ (x y : A) → x < y → ¬ (y ≤ x)
    <-introd : ∀ (x y : A) → x ≤ y → ¬ (y ≤ x) → x < y
    <-splits : ∀ (x y : A) → x ≤ y → x < y ⊎ x ≡ y
open cor[<] {{...}} public

postulate
  instance
    cor[<][ℕ] : cor[<] ℕ

record has[∇] (A : Set) : Set where
  infix 14 _∇_
  field
    _∇_ : A → A → Comparison
open has[∇] {{...}} public

instance
  has[∇][ℕ] : has[∇] ℕ
  has[∇][ℕ] = record { _∇_ = _∇ᴺ_ }

data Ordering[_] {A : Set} (_≺_ : A → A → Set) (x y : A) : Set where
  LT : x ≺ y → Ordering[ _≺_ ] x y
  EQ : x ≡ y → Ordering[ _≺_ ] x y
  GT : y ≺ x → Ordering[ _≺_ ] x y

data Link[_] {A : Set} (_≺_ : A → A → Set) {x y : A} : Comparison → Ordering[ _≺_ ] x y → Set where
  LT : ∀ {ε : x ≺ y} → Link[ _≺_ ] LT (LT ε)
  EQ : ∀ {ε : x ≡ y} → Link[ _≺_ ] EQ (EQ ε)
  GT : ∀ {ε : y ≺ x} → Link[ _≺_ ] GT (GT ε)

record cor[∇] (A : Set) {{_ : has[∇] A}} {{_ : has[<] A}} : Set₁ where
  field
    _∇?_ : ∀ (x y : A) → Ordering[ _<_ ] x y
    _∇!_ : ∀ (x y : A) → Link[ _<_ ] (x ∇ y) (x ∇? y)
open cor[∇] {{...}} public

postulate
  instance
    cor[∇][ℕ] : cor[∇] ℕ

_ : 3 ∇ 4 ≡ LT
_ = refl

module _ {A : Set} {{_ : has[∇] A}} where

  insert : A → List A → List A
  insert x [] = x ∷ []
  insert x (y ∷ ys) with x ∇ y
  … | LT = x ∷ y ∷ ys
  … | EQ = x ∷ y ∷ ys
  … | GT = y ∷ insert x ys
  
  sort : List A → List A
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs)

module _ {A : Set} {{_ : has[<] A}} where

  data _≤[List]_ (x : A) : List A → Set where
    [] : x ≤[List] []
    ⟨_⟩ : ∀ {y ys}
      → x ≤ y
      → x ≤[List] (y ∷ ys)
  
  data Sorted : List A → Set where
    [] : Sorted []
    _∷_ : ∀ {x xs}
      → x ≤[List] xs
      → Sorted xs
      → Sorted (x ∷ xs)

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[∇] A}} {{_ : cor[∇] A}} where 

  ≤[List]-trans : ∀ (x y : A) (xs : List A) → y ≤[List] xs → x ≤ y → x ≤[List] xs
  ≤[List]-trans x y xs [] ε₂ = []
  ≤[List]-trans x y (x′ ∷ xs) ⟨ ε₁ ⟩ ε₂ = ⟨ ≤-trans x y x′ ε₁ ε₂ ⟩

  ≤[List]-insert : ∀ (x y : A) (xs : List A) → x ≤ y → x ≤[List] xs → x ≤[List] insert y xs
  ≤[List]-insert x y [] ε₁ ε₂ = ⟨ ε₁ ⟩
  ≤[List]-insert x y (z ∷ xs) ε₁ ⟨ ε₂ ⟩ with y ∇ z
  … | LT = ⟨ ε₁ ⟩
  … | EQ = ⟨ ε₁ ⟩
  … | GT = ⟨ ε₂ ⟩

  Sorted[insert] : ∀ (x : A) (xs : List A) → Sorted xs → Sorted (insert x xs)
  Sorted[insert] x [] ε = [] ∷ ε
  Sorted[insert] x (y ∷ xs) (ε ∷ εs) with x ∇ y | x ∇? y | x ∇! y
  … | LT | LT ε′ | LT = ⟨ <-weaken x y ε′ ⟩ ∷ (ε ∷ εs)
  … | EQ | EQ ε′ | EQ rewrite ε′ = ⟨ ≤-refl y ⟩ ∷ ε ∷ εs
  … | GT | GT ε′ | GT = ≤[List]-insert y x xs (<-weaken y x ε′) ε ∷ Sorted[insert] x xs εs
  
  Sorted[sort] : ∀ xs → Sorted (sort xs)
  Sorted[sort] [] = []
  Sorted[sort] (x ∷ xs) with Sorted[sort] xs
  … | IH = Sorted[insert] x (sort xs) IH
