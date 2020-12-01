module IC12 where

---------
-- LIB --
---------

-- equality --

infix 8 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  instance
    ↯ : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

-- booleans --

data 𝔹 : Set where
  I : 𝔹
  O : 𝔹

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

data <! : Set where
  [<] : <!
  [≥] : <!

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

_<?_ : ℕ → ℕ → <!
_ <? Z = [≥]
Z <? S n = [<]
S m <? S n = m <? n

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

length[list] : ∀ {A : Set} → list A → ℕ
length[list] [] = 0
length[list] (x ∷ xs) = 1 + length[list] xs

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

  runit[⧺] : ∀ (ms : list ℕ) → ms ⧺ [] ≡ ms
  assoc[⧺] : ∀ (ms ns ps : list ℕ) → ms ⧺ (ns ⧺ ps) ≡ (ms ⧺ ns) ⧺ ps

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

-- well-founded --

data acc (x : ℕ) : Set where
  Acc : (∀ {y} → y < x → acc y) → acc x

acc[<] : ∀ {m} (n : ℕ) → m < n → acc m
acc[<] Z ()
acc[<] (S n) Z = Acc λ where ()
acc[<] (S n) (S ε) = Acc λ where ε′ → (acc[<] n) ( to[</≤] ε ⊚[≤/<] ε′)

wf[<] : ∀ (n : ℕ) → acc n
wf[<] n = Acc (acc[<] n)

-- vectors --

data vec (A : Set) : ℕ → Set where
  [] : vec A Z
  _∷_ : ∀ {n} → A → vec A n → vec A (S n)

vec[_] : ℕ → Set → Set
vec[ n ] A = vec A n
{-# DISPLAY vec A n = vec[ n ] A #-}

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

graph[_] : ℕ → Set
graph[ n ] = matrix[ n , n ] 𝔹

---------------
-- EXERCISES --
---------------

data idx : ℕ → Set where
  Z : ∀ {n} → idx (S n)
  S : ∀ {n} → idx n → idx (S n)

infixl 40 _#[_]
_#[_] : ∀ {A : Set} {n : ℕ} → vec[ n ] A → idx n → A
xs #[ ι ] = {!!}

infixl 40 _#[_↦_]
_#[_↦_] : ∀ {A n} → vec[ n ] A → idx n → A → vec[ n ] A
xs #[ ι ↦ x ] = {!!}

build[_] : ∀ {A : Set} (n : ℕ) → (idx n → A) → vec[ n ] A
build[ n ] f = {!!}

reduc[build/#] : ∀ {A : Set} {n : ℕ} (ι : idx n) (f : idx n → A) → build[ n ] f #[ ι ] ≡ f ι
reduc[build/#] ι f = {!!}

ext[vec] : ∀ {A n} (xs ys : vec[ n ] A) → (∀ (ι : idx n) → xs #[ ι ] ≡ ys #[ ι ]) → xs ≡ ys
ext[vec] xs ys p = {!!}

tr : ∀ {A m n} → matrix[ m , n ] A → matrix[ n , m ] A
tr xs = {!!}

vec-iter : ∀ {A B : Set} {n} → vec[ n ] A → B → (idx n → A → B → B) → B
vec-iter xs i f = {!!}

{-# TERMINATING #-}
dfs′ : ∀ {n} → idx n → graph[ n ] → vec[ n ] 𝔹 → list (idx n) ∧ vec[ n ] 𝔹
dfs′ ι₀ G σ = {!!}

const[vec]<_> : ∀ {A : Set} (m : ℕ) → A → vec[ m ] A
const[vec]< m > x = {!!}

dfs : ∀ {n} → graph[ n ] → idx n → list (idx n)
dfs G ι = {!!}

-- 0 -> 1
-- 0 -> 3
-- 1 -> 4
-- 2 -> 1
-- 2 -> 4
-- 3 -> 0
-- 3 -> 2
-- 4 -> 0
G1 : graph[ 5 ]
G1 = [ [ O , I , O , I , O ]
     , [ O , O , O , O , I ]
     , [ O , I , O , O , I ]
     , [ I , O , I , O , O ]
     , [ I , O , O , O , O ]
     ]

𝕚 : ∀ (m : ℕ) {n} {{_ : m <? n ≡ [<]}} → idx n
𝕚 m {n} {{ε}} = {!!}

_ : dfs G1 Z ≡ [ 𝕚 0 , 𝕚 1 , 𝕚 4 , 𝕚 3 , 𝕚 2 ]
_ = {!!}

{-

# Project Proposal

Members of your group:

Algorithm or datastructure name:

Algorithm or datastructure reference:

Theorem(s) you plan to prove:

Datatypes you will use or need:

Fallback plan (if things get harder than you thought):

-}
