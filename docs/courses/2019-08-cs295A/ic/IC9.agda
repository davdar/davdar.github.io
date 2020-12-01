module IC9 where

---------
-- LIB --
---------

-- equality --

infix 8 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

-- booleans --

data 𝔹 : Set where
  T : 𝔹
  F : 𝔹

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

-- order --

infix 8 _≤_
data _≤_ : ℕ → ℕ → Set where
  Z : ∀ {n} → Z ≤ n
  S : ∀ {m n} → m ≤ n → S m ≤ S n

infix 8 _<_
data _<_ : ℕ → ℕ → Set where
  Z : ∀ {n} → Z < S n
  S : ∀ {m n} → m < n → S m < S n

data ≤! : Set where
  [≤] : ≤!
  [>] : ≤!

infix 8 _≤⋆!_
data _≤⋆!_ (m n : ℕ) : Set where
  [≤] : m ≤ n → m ≤⋆! n
  [>] : n < m → m ≤⋆! n

data ⋚! : Set where
  [<] : ⋚!
  [≡] : ⋚!
  [>] : ⋚!

infix 8 _⋚⋆!_
data _⋚⋆!_ (m n : ℕ) : Set where
  [<] : m < n → m ⋚⋆! n
  [≡] : m ≡ n → m ⋚⋆! n
  [>] : n < m → m ⋚⋆! n

_≤?_ : ℕ → ℕ → ≤!
Z ≤? n = [≤]
S m ≤? Z = [>]
S m ≤? S n = m ≤? n

_⋚?_ : ℕ → ℕ → ⋚!
Z ⋚? Z = [≡]
Z ⋚? S n = [<]
S m ⋚? Z = [>]
S m ⋚? S n = m ⋚? n

-- type-level connectives --

data 𝟘 : Set where

infixr 9 ¬_
¬_ : Set → Set
¬ A = A → 𝟘

data 𝟙 : Set where
  • : 𝟙

infix 5 _∨_
data _∨_ (A B : Set) : Set where
  Inl : A → A ∨ B
  Inr : B → A ∨ B

infix 6 _∧_
record _∧_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    π₁ : A
    π₂ : B
open _∧_

data existential (A : Set) (B : A → Set) : Set where
  ⟨∃_,_⟩ : ∀ (x : A) → B x → existential A B

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

length : ∀ {A : Set} → list A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

infix 8 _≤[first]_
data _≤[first]_ (m : ℕ) : list ℕ → Set where
  [] : m ≤[first] []
  ⟨_⟩ : ∀ {n ns}
    → m ≤ n
    → m ≤[first] n ∷ ns

data sorted : list ℕ → Set where
  [] : sorted []
  _∷_ : ∀ {x xs}
    → x ≤[first] xs
    → sorted xs
    → sorted (x ∷ xs)

infix 8 _≤[all]_
data _≤[all]_ (x : ℕ) : list ℕ → Set where
  [] : x ≤[all] []
  _∷_  : ∀ {y : ℕ} {ys : list ℕ}
    → x ≤ y
    → x ≤[all] ys
    → x ≤[all] (y ∷ ys)

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

infixl 18 _⊚[≡]_
infixl 18 _⊚[≤]_
infixl 17 _⋈[≤]_

postulate
  _⊚[≡]_ : ∀ {A} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
  ◇[≡] : ∀ {A} {x y : A} → x ≡ y → y ≡ x

  runit[+] : ∀ (m : ℕ) → m + 0 ≡ m
  assoc[+] : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
  commu[+] : ∀ (m n : ℕ) → m + n ≡ n + m

  lmono[+] : ∀ {m n} p → m ≤ n → m + p ≤ n + p
  rmono[+] : ∀ m {n p} → n ≤ p → m + n ≤ m + p

  runit[×] : ∀ (m : ℕ) → m × 1 ≡ m
  rzero[×] : ∀ (m : ℕ) → m × 0 ≡ 0
  assoc[×] : ∀ (m n p : ℕ) → m × (n × p) ≡ (m × n) × p
  commu[×] : ∀ (m n : ℕ) → m × n ≡ n × m
  ldist[×] : ∀ (m n p : ℕ) → m × (n + p) ≡ m × n + m × p
  rdist[×] : ∀ (m n p : ℕ) → (m + n) × p ≡ m × p + n × p

  xRx[≤] : ∀ (m : ℕ) → m ≤ m
  _⊚[≤]_ : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
  _⋈[≤]_ : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n

  ¬xRx[<] : ∀ {m : ℕ} → m < m → 𝟘
  _⊚[<]_ : ∀ {m n p : ℕ} → n < p → m < n → m < p
  _⊚[</≤]_ : ∀ {m n p : ℕ} → n < p → m ≤ n → m < p
  _⊚[≤/<]_ : ∀ {m n p : ℕ} → n ≤ p → m < n → m < p
  _¬◇_ : ∀ {m n : ℕ} → m < n → n < m → 𝟘

  s[≤] : ∀ (m : ℕ) → m ≤ S m
  s[<] : ∀ (m : ℕ) → m < S m

  to[</≤] : ∀ {m n : ℕ} → m < n → S m ≤ n
  fr[</≤] : ∀ {m n : ℕ} → S m ≤ n → m < n

  to[≤/<] : ∀ {m n : ℕ} → m ≤ n → m < S n
  fr[≤/<] : ∀ {m n : ℕ} → m < S n → m ≤ n

  wk[<] : ∀ {m n : ℕ} → m < n → m ≤ n
  in[≤] : ∀ {m n : ℕ} → m ≤ n → m < n ∨ m ≡ n

  snd[≤?/≤] : ∀ {m n : ℕ} → m ≤? n ≡ [≤] → m ≤ n
  snd[≤?/>] : ∀ {m n : ℕ} → m ≤? n ≡ [>] → n < m

  cmp[≤?/≤] : ∀ {m n : ℕ} → m ≤ n → m ≤? n ≡ [≤]
  cmp[≤?/>] : ∀ {m n : ℕ} → n < m → m ≤? n ≡ [>]

  snd[⋚?/<] : ∀ {m n : ℕ} → m ⋚? n ≡ [<] → m < n
  snd[⋚?/≡] : ∀ {m n : ℕ} → m ⋚? n ≡ [≡] → m ≡ n
  snd[⋚?/>] : ∀ {m n : ℕ} → m ⋚? n ≡ [>] → n < m

  cmp[⋚?/<] : ∀ {m n : ℕ} → m < n → m ⋚? n ≡ [<]
  cmp[⋚?/≡] : ∀ {m n : ℕ} → m ≡ n → m ⋚? n ≡ [≡]
  cmp[⋚?/>] : ∀ {m n : ℕ} → n < m → m ⋚? n ≡ [>]

  _≤⋆_ : ∀ (m n : ℕ) → m ≤⋆! n
  _⋚⋆_ : ∀ (m n : ℕ) → m ⋚⋆! n


-- ======== --
-- IN CLASS --
-- ======== --

-----------------
-- DEFINITIONS --
-----------------

-- selection sort --

find-min : ℕ → list ℕ → ℕ ∧ list ℕ
find-min x [] = ⟨ x , [] ⟩
find-min x (y ∷ ys) with x ≤? y
… | [≤] = let ⟨ m , zs ⟩ = find-min x ys in ⟨ m , y ∷ zs ⟩
… | [>] = let ⟨ m , zs ⟩ = find-min y ys in ⟨ m , x ∷ zs ⟩

{-# TERMINATING #-}
ssort : list ℕ → list ℕ
ssort [] = []
ssort (x ∷ xs) with find-min x xs
… | ⟨ m , ys ⟩ = m ∷ ssort ys

---------------
-- EXERCISES --
---------------

postulate
  find-min-length : ∀ (x : ℕ) (ys : list ℕ) → let ⟨ m , zs ⟩ = find-min x ys in length ys ≡ length zs

ssort-t : ∀ (n : ℕ) (xs : list ℕ) → length xs ≡ n → list ℕ
ssort-t n xs ε = {!!}

-- merge sort --

split′ : list ℕ → list ℕ ∧ list ℕ
split′ xs = {!!}

split : list ℕ → list ℕ ∧ list ℕ
split xs = {!!}

merge : list ℕ → list ℕ → list ℕ
merge xs ys = {!!}

{-# TERMINATING #-}
msort-nt : list ℕ → list ℕ
msort-nt xs = {!!}

-- well-founded relations --

data acc (x : ℕ) : Set where
  Acc : (∀ {y} → y < x → acc y) → acc x

acc[<] : ∀ {m} (n : ℕ) → m < n → acc m
acc[<] n ε = {!!}

wf[<] : ∀ (n : ℕ) → acc n
wf[<] n = {!!}

postulate
  split-length : ∀ (xs : list ℕ) → let ⟨ ys , zs ⟩ = split xs in length ys ≤ length xs ∧ length zs ≤ length xs

msort-rec : ∀ (xs : list ℕ) → acc (length xs) → list ℕ
msort-rec xs a = {!!}

msort : list ℕ → list ℕ
msort xs = {!!}
