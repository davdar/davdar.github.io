-- [Nearly all of this material is borrowed from [plfa.Lists]
-- authored by Wen Kokke and Philip Wadler.]
-- 
-- [plfa.Lists]: https://plfa.github.io/Lists/

module la10 where

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
  zero : ∀ {n : ℕ} → zero ≤ n
  suc : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  zero : ∀ {n : ℕ} → zero < suc n
  suc : ∀ {m n : ℕ} → m < n → suc m < suc n

infixr 2 _×_
data _×_ : Set → Set → Set where
  ⟨_,_⟩ : ∀ {A B : Set}
    → A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

infix 1 _⊎_
data _⊎_ : Set → Set → Set where
  inj₁ : ∀ {A B : Set} → A → A ⊎ B
  inj₂ : ∀ {A B : Set} → B → A ⊎ B

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

infix 20 ¬_
¬_ : Set → Set
¬ A = A → ⊥

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
  -- < --
  <-irrefl : ∀ (m : ℕ) → ¬ (m ≤ m)
  <-trans : ∀ {m n p : ℕ} → n < p → m < n → m < p
  <-asym : ∀ {m n : ℕ} → ¬ (m < n × n < m)

--------------
-- IN CLASS --
--------------

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

_ : List ℕ
_ = [ 0 , 1 , 2 ]

infixl 6 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_ : [ 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 1 , 2 , 3 , 4 ]
_ = refl

++-lunit : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-lunit xs = refl

++-runit : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-runit [] = refl
++-runit (x ∷ xs) rewrite ++-runit xs = refl

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

++-length : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
++-length [] ys = refl
++-length (x ∷ xs) ys rewrite ++-length xs ys = refl

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

module Hide where
  shunt-reverse : ∀ {A : Set} (xs : List A) → shunt xs [] ≡ reverse xs
  shunt-reverse xs = {!!}

shunt-reverse-strong : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse-strong [] ys = refl
shunt-reverse-strong (x ∷ xs) ys rewrite shunt-reverse-strong xs (x ∷ ys) | ++-assoc (reverse xs) [ x ] ys = refl

shunt-reverse : ∀ {A : Set} (xs : List A) → shunt xs [] ≡ reverse xs
shunt-reverse xs rewrite shunt-reverse-strong xs [] | ++-runit (reverse xs) = refl

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

sucs : List ℕ → List ℕ
sucs xs = map (λ n → suc n) xs

_ : sucs [ 1 , 2 , 3 ] ≡ [ 2 , 3 , 4 ]
_ = refl

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr f i [] = i
foldr f i (x ∷ xs) = f x (foldr f i xs)

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ = refl

_ : foldr _*_ 1 [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

_ : foldr (λ x xs → x ∷ xs) [] [ 1 , 2 , 3 ] ≡ [ 1 , 2 , 3 ]
_ = refl

foldl : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldl f i [] = i
foldl f i (x ∷ xs) = foldl f (f x i) xs


_ : foldl _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ = refl

_ : foldl _*_ 1 [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

_ : foldl (λ x xs → x ∷ xs) [] [ 1 , 2 , 3 ] ≡ [ 3 , 2 , 1 ]
_ = refl

length-as-foldl : ∀ {A : Set} → List A → ℕ
length-as-foldl = foldl (λ _ n → suc n) 0

_ : length-as-foldl [ 1 , 2 , 3 ] ≡ 3
_ = refl

map-as-foldr : ∀ {A B : Set} → (A → B) → List A → List B
map-as-foldr f = foldr (λ x ys → f x ∷ ys) []

_ : map-as-foldr (λ n → 10 + n) [ 1 , 2 , 3 ] ≡ [ 11 , 12 , 13 ]
_ = refl

reverse-as-foldl : ∀ {A : Set} → List A → List A
reverse-as-foldl = foldl (λ x xs → x ∷ xs) []

_ : reverse-as-foldl [ 1 , 2 , 3 ] ≡ [ 3 , 2 , 1 ]
_ = refl

reverse-as-foldr : ∀ {A : Set} → List A → List A
reverse-as-foldr xs = foldr (λ x k xs → k (x ∷ xs)) (λ x → x) xs []

_ : reverse-as-foldr [ 1 , 2 , 3 ] ≡ [ 3 , 2 , 1 ]
_ = refl
