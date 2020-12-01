module IC11 where

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

-----------------
-- DEFINITIONS --
-----------------

-- vectors are lists which know their length --
data vec (A : Set) : ℕ → Set where
  [] : vec A Z
  _∷_ : ∀ {n} → A → vec A n → vec A (S n)

-- this just tells Agda to display vectors as `vec[ m ] A` instead of
-- `vec A m`
vec[_] : ℕ → Set → Set
vec[ n ] A = vec A n
{-# DISPLAY vec A n = vec[ n ] A #-}

-- these patterns work for both lists and vectors
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

-- matrices (which know their dimensions) are just vectors of vectors
-- (which know their lengths)
matrix[_,_] : ℕ → ℕ → Set → Set
matrix[ m , n ] A = vec[ m ] (vec[ n ] A)

---------------
-- EXERCISES --
---------------

-- an example vector --
_ : vec[ 4 ] ℕ
_ = {!!}

-- an example matrix --
_ : matrix[ 2 , 3 ] ℕ
_ = {!!}

-- the length function on vectors
length : ∀ {A : Set} {m : ℕ} → vec[ m ] A → ℕ
length xs = {!!}

-- alwas returns the same number as the index `m`
known-length : ∀ {A : Set} {m : ℕ} (xs : vec[ m ] A) → length xs ≡ m
known-length xs = {!!}

-- we can define dot-product; notice how we know that the vectors have
-- the same length, so never have to deal with a [] on the left when
-- there is a _∷_ on the right
infixl 16 _⋅_
_⋅_ : ∀ {m : ℕ} → vec[ m ] ℕ → vec[ m ] ℕ → ℕ
xs ⋅ ys = {!!}

-- concatenating two vectors; the new length is the sum of lengths
infixl 15 _⧻_
_⧻_ : ∀ {A : Set} {m n : ℕ} → vec[ m ] A → vec[ n ] A → vec[ m + n ] A
xs ⧻ ys = {!!}

-- reversing a vector; requires using a lemma in order to typecheck
reverse : ∀ {A : Set} {m : ℕ} → vec[ m ] A → vec[ m ] A
reverse xs = {!!}

-- map for vectors is just like lists
map : ∀ {A B : Set} {m : ℕ} → (A → B) → vec[ m ] A → vec[ m ] B
map f xs = {!!}

-- concat-map for vectors is also just like lists; the final length is
-- a multiplication; how cool is that?
concat-map : ∀ {A B : Set} {m n : ℕ} → vec[ m ] A → (A → vec[ n ] B) → vec[ m × n ] B
concat-map xs f = {!!}

-- this gives us access to “do notation”
infixr 2 _>>=_
_>>=_ : ∀ {A B : Set} {m n : ℕ} → vec[ m ] A → (A → vec[ n ] B) → vec[ m × n ] B
_>>=_ = concat-map

-- a fancy name for the “singleton” vector
return : ∀ {A : Set} → A → vec[ 1 ] A
return x = {!!}

-- cartesian product for vectors; the final length is a multiplication
-- because it uses concat-map; again we need to use a lemma in order
-- to typecheck
infixl 16 _⨳_
_⨳_ : ∀ {A B} {m n : ℕ} (xs : vec[ m ] A) (ys : vec[ n ] B) → vec[ m × n ] (A ∧ B)
xs ⨳ ys = {!!}

-- remember selection sort on lists?

find-min[list] : ℕ → list ℕ → ℕ ∧ list ℕ
find-min[list] x [] = ⟨ x , [] ⟩
find-min[list] x (y ∷ ys) with x ≤? y
… | [≤] =
  let ⟨ x , zs ⟩ = find-min[list] x ys
  in ⟨ x , y ∷ zs ⟩
… | [>] =
  let ⟨ x , zs ⟩ = find-min[list] y ys
  in ⟨ x , x ∷ zs ⟩

{-# TERMINATING #-}
ssort[list] : list ℕ → list ℕ
ssort[list] [] = []
ssort[list] (x ∷ xs) =
  let ⟨ x , ys ⟩ = find-min[list] x xs
  in x ∷ ssort[list] ys

-- the termination proof for selection sort was painful; with vectors
-- it's very easy:

find-min : ∀ {m : ℕ} → ℕ → vec[ m ] ℕ → ℕ ∧ vec[ m ] ℕ
find-min x [] = ⟨ x , [] ⟩
find-min x (y ∷ ys) with x ≤? y
… | [≤] = {!!}
… | [>] = {!!}

-- Agda accepts this because lists know their length, and `ys` in the
-- recursive call is of strictly smaller length. In order for this to
-- work, `find-min` must return a list with length equal to the input
-- list
ssort : ∀ {m : ℕ} → vec[ m ] ℕ → vec[ m ] ℕ
ssort xs = {!!}

-- if you want to work with graphs for your final project, a nice
-- representation is an adjacency matrix (i.e., a matrix of booleans)
-- which indicates which nodes have an edge to which other nodes. If
-- you want to annotate edges with information you can use an “option”
-- instead of a boolean.
graph : ℕ → Set
graph n = matrix[ n , n ] 𝔹
