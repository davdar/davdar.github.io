{-
Name: ⁇
Date: ⁇

Collaboration & Resources Statement:
«Write your statement here…»
-}

---------------
-- LOGISTICS --
---------------

-- To submit the assignment, upload your solution to Gradescope as a
-- single .agda file.
--
-- Make sure you write your name, the date, and your collaboration
-- & Resources statement above, as indicated by the course
-- collaboration and resources policy:
--
--     Collaboration on the high-level ideas and approach on assignments
--     is encouraged. Copying someone else's work is not allowed. Copying
--     solutions from an online source is not allowed. Any collaboration
--     or online resources, even if used only at a high level, must be
--     declared when you submit your assignment. Every assignment must
--     include a collaboration and resources statement. E.g., “I discussed
--     high-level strategies for solving problem 2 and 5 with Alex; I
--     found this stackoverflow post helpful while working on problem 3 ”
--     Students caught copying work are eligible for immediate failure of
--     the course and disciplinary action by the University. All academic
--     integrity misconduct will be treated according to UVM's Code of
--     Academic Integrity.
--
-- This assignment consists of a LIB section which contains relevant
-- definitions and lemmas which you should refer to throughout the
-- assignment, and an ASSIGNMENT section which contains definitions
-- and lemmas with “holes” in them. *If you only change the code
-- within the holes and your entire assignment compiles without
-- errors, you are guaranteed 100% on the assignment.*

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

_⩓_ : 𝔹 → 𝔹 → 𝔹
O ⩓ _ = O
_ ⩓ O = O
I ⩓ I = I

_⩔_ : 𝔹 → 𝔹 → 𝔹
I ⩔ _ = I
_ ⩔ I = I
O ⩔ O = O

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

matrix[_,_] : ℕ → ℕ → Set → Set
matrix[ m , n ] A = vec[ m ] (vec[ n ] A)

graph[_] : ℕ → Set
graph[ n ] = matrix[ n , n ] 𝔹

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

-----------------
-- DEFINITIONS --
-----------------

data idx : ℕ → Set where
  Z : ∀ {n} → idx (S n)
  S : ∀ {n} → idx n → idx (S n)

𝕚 : ∀ (m : ℕ) {n} {{_ : m <? n ≡ [<]}} → idx n
𝕚 Z {Z} {{()}}
𝕚 Z {S n} {{↯}} = Z
𝕚 (S m) {Z} {{()}}
𝕚 (S m) {S n} = S (𝕚 m {n})

infixl 40 _#[_]
_#[_] : ∀ {A : Set} {n : ℕ} → vec[ n ] A → idx n → A
(x ∷ xs) #[ Z ] = x
(x ∷ xs) #[ S ι ] = xs #[ ι ]

infixl 40 _#[_↦_]
_#[_↦_] : ∀ {A n} → vec[ n ] A → idx n → A → vec[ n ] A
(x ∷ xs) #[ Z ↦ x′ ] = x′ ∷ xs
(x ∷ xs) #[ S ι ↦ x′ ] = x ∷ (xs #[ ι ↦ x′ ])
vec-iter : ∀ {A B : Set} {n} → vec[ n ] A → B → (idx n → A → B → B) → B
vec-iter [] i f = i
vec-iter (x ∷ xs) i f = vec-iter xs (f Z x i) (λ ι x y → f (S ι) x y)

build[_] : ∀ {A : Set} (n : ℕ) → (idx n → A) → vec[ n ] A
build[ Z ] f = []
build[ S n ] f = f Z ∷ build[ n ] (λ ι → f (S ι))

const[vec]<_> : ∀ {A : Set} (m : ℕ) → A → vec[ m ] A
const[vec]< Z > x = []
const[vec]< S m > x = x ∷ const[vec]< m > x 

{-# TERMINATING #-}
dfs-rec : ∀ {n} → idx n → graph[ n ] → vec[ n ] 𝔹 → list (idx n) ∧ vec[ n ] 𝔹
dfs-rec ι₀ G σ with σ #[ ι₀ ]
… | I = ⟨ [] , σ ⟩
… | O = vec-iter (G #[ ι₀ ]) ⟨ [ ι₀ ] , σ #[ ι₀ ↦ I ] ⟩
                 (λ where ι O ⟨ xs , S′ ⟩ → ⟨ xs , S′ ⟩
                          ι I ⟨ xs , S′ ⟩ → 
                            let ⟨ xs′ , S″ ⟩ = dfs-rec ι G S′
                            in ⟨ xs ⧺ xs′ , S″ ⟩)
dfs : ∀ {n} → graph[ n ] → idx n → list (idx n)
dfs G ι = π₁ (dfs-rec ι G (const[vec]< _ > O))

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

_ : dfs G1 Z ≡ [ 𝕚 0 , 𝕚 1 , 𝕚 4 , 𝕚 3 , 𝕚 2 ]
_ = ↯

---------------
-- EXERCISES --
---------------

-- E1: [★★★]
-- Define a function which detects whether or not there is a cycle in
-- a graph which is reachable from a root node.
-- HINTS:
-- ‣ use implementation of `dfs-rec` and `dfs` as inspiration
-- ‣ notice the implementation of logical “and” and “or” have been
--   added to the lib above (written ⩓ and ⩔ and typed as \hand and
--   \hor mnemonic for “heavy and” and “heavy or”).
-- ‣ understand the examples below before starting to implement
-- ‣ be careful: if you write a definition for `cycle-rec` which
--   doesn't terminate, it will cause Agda's typechecker to loop
--   forever. If this happens do `C-c C-x C-r` or click the menu option
--   for `Agda > Kill and restart Agda`.
{-# TERMINATING #-}
cycle-rec :
  ∀ {n}             -- number of nodes in the graph
  → idx n           -- node to start the cycle detection search from
  → graph[ n ]      -- the graph
  → vec[ n ] 𝔹      -- nodes seen so far
  → 𝔹 ∧ vec[ n ] 𝔹 -- the boolean result (if a cycle was detected or not) and the new “seen set”
cycle-rec ι₀ G σ = {!!}

cycle : ∀ {n} → graph[ n ] → idx n → 𝔹
cycle G ι = π₁ (cycle-rec ι G (const[vec]< _ > O))

-- EXAMPLES --

G2 : graph[ 2 ]
G2 = [ [ O , I ]
     , [ O , O ]
     ]

G3 : graph[ 2 ]
G3 = [ [ I , O ]
     , [ O , O ]
     ]

G4 : graph[ 2 ]
G4 = [ [ O , I ]
     , [ I , O ]
     ]

G5 : graph[ 2 ]
G5 = [ [ O , I ]
     , [ O , I ]
     ]

G6 : graph[ 2 ]
G6 = [ [ O , O ]
     , [ I , I ]
     ]

G7 : graph[ 2 ]
G7 = [ [ I , I ]
     , [ O , O ]
     ]

_ : cycle G2 Z ≡ O
_ = ↯

_ : cycle G3 Z ≡ I
_ = ↯

_ : cycle G4 Z ≡ I
_ = ↯

_ : cycle G5 Z ≡ I
_ = ↯

_ : cycle G6 Z ≡ O
_ = ↯

_ : cycle G7 Z ≡ I
_ = ↯

-- E2: [★☆☆]
-- Fill out the project proposal below. To do so, you must create an
-- account on GitHub (https://github.com) if you don't already have
-- one.

{-

# Project Proposal

Members of your group:

(names)

GitHub ids for all members of your group:

(ids)

Algorithm or datastructure name:

(e.g., AVL trees.)

Algorithm or datastructure reference: 

(e.g., a website or paper)

Theorem(s) you plan to prove:

(e.g., elements in datastructre are well-balanced.)

Datatypes you will use or need not already provided: 

(e.g., sets, stacks, queues, real numbers, hashing functions, etc.)

Minimum Viable Product (MVP): 

(what is the smallest version of your algorithm that you can
definitely deliver? e.g., what is the largest set of simplifications
you can make such that the project is still interesting?)

-}
