module IC7 where

---------
-- LIB --
---------

-- equality --

infix 8 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

-- naturals --

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 15 _+_
_+_ : ℕ → ℕ → ℕ
Z    + n  =  n
(S m) + n  =  S (m + n)

infixl 16 _×_
_×_ : ℕ → ℕ → ℕ
Z × _ = Z
S m × n = n + m × n

-- pairs --

infix 6 _∧_
data _∧_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A ∧ B

-- lists --

infixr 20 _∷_
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

infixl 16 _⧺_
_⧺_ : ∀ {A : Set} → list A → list A → list A
[] ⧺ ys = ys
(x ∷ xs) ⧺ ys = x ∷ (xs ⧺ ys)

-- functions -- 

id : ∀ {A : Set} → A → A
id x = x

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- POSTULATES --

postulate
  reduc[+] : ∀ (m n : ℕ) → m + S n ≡ S (m + n)
  runit[+] : ∀ (m : ℕ) → m + 0 ≡ m
  assoc[+] : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
  commu[+] : ∀ (m n : ℕ) → m + n ≡ n + m

  runit[×] : ∀ (m : ℕ) → m × 1 ≡ m
  rzero[×] : ∀ (m : ℕ) → m × 0 ≡ 0
  assoc[×] : ∀ (m n p : ℕ) → m × (n × p) ≡ (m × n) × p
  commu[×] : ∀ (m n : ℕ) → m × n ≡ n × m
  ldist[×] : ∀ (m n p : ℕ) → m × (n + p) ≡ m × n + m × p
  rdist[×] : ∀ (m n p : ℕ) → (m + n) × p ≡ m × p + n × p

--------------
-- IN CLASS --
--------------

reverse : ∀ {A : Set} → list A → list A
reverse xs = {!!}

map : ∀ {A B : Set} → (A → B) → list A → list B
map f xs = {!!}

runit[⧺] : ∀ {A} (xs : list A) → xs ⧺ [] ≡ xs
runit[⧺] xs = {!!}

assoc[⧺] : ∀ {A} (xs ys zs : list A) → xs ⧺ (ys ⧺ zs) ≡ (xs ⧺ ys) ⧺ zs
assoc[⧺] xs ys zs = {!!}

pair-with₁ : ∀ {A B} (x : A) → (ys : list B) → list (A ∧ B)
pair-with₁ x ys = {!!}

pair-with₂ : ∀ {A B} (x : A) → (ys : list B) → list (A ∧ B)
pair-with₂ x ys = {!!}

_⨳_ : ∀ {A B} (xs : list A) (ys : list B) → list (A ∧ B)
xs ⨳ ys = {!!}

ldist[⨳] : ∀ {A B} (xs : list A) (ys : list A) (zs : list B) → (xs ⧺ ys) ⨳ zs ≡ (xs ⨳ zs) ⧺ (ys ⨳ zs)
ldist[⨳] xs ys zs = {!!}

foldl-on : ∀ {A B : Set} → list A → B → (A → B → B) → B
foldl-on xs y f = {!!}

foldr-on : ∀ {A B : Set} → list A → B → (A → B → B) → B
foldr-on xs y f = {!!}

other-⨳ : ∀ {A B} (xs : list A) (ys : list B) → list (A ∧ B)
other-⨳ xs ys = {!!}

other-⨳-correct : ∀ {A B} (xs : list A) (ys : list B) → xs ⨳ ys ≡ other-⨳ xs ys
other-⨳-correct xs ys = {!!}

infixr 1 _$_
_$_ : ∀ {A B : Set} → (A → B) → A → B
f $ x = f x

map-on : ∀ {A B : Set} → list A → (A → B) → list B
map-on xs f = {!!}

list-id : ∀ {A} → list A → list A
list-id ys = {!!}

reverse′ : ∀ {A} → list A → list A
reverse′ ys = {!!}

concat : ∀ {A : Set} → list (list A) → list A
concat yss = {!!}

other-⨳′ : ∀ {A B} (xs : list A) (ys : list B) → list (A ∧ B)
other-⨳′ xs ys = {!!}

concat-map : ∀ {A B} → list A → (A → list B) → list B
concat-map xs f = {!!}

infixr 2 _>>=_
_>>=_ : ∀ {A B} → list A → (A → list B) → list B
_>>=_ = concat-map

other-⨳″ : ∀ {A B} (xs : list A) (ys : list B) → list (A ∧ B)
other-⨳″ xs ys = {!!}

return : ∀ {A} → A → list A
return x = {!!}

other-⨳‴ : ∀ {A B} (xs : list A) (ys : list B) → list (A ∧ B)
other-⨳‴ xs ys = {!!}

other-map-on : ∀ {A B} (xs : list A) (f : A → B) → list B
other-map-on xs f = {!!}
