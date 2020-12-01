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

module HW6 where

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

-- ========= --
-- ASIGNMENT --
-- ========= --

-----------------
-- DEFINITIONS --
-----------------

-- This function takes the first and rest of a list, and returns the
-- minimum element of that list paired with the original list with the
-- minimum removed
find-min : ℕ → list ℕ → ℕ ∧ list ℕ
find-min x [] = ⟨ x , [] ⟩
find-min x (y ∷ ys) with x ≤? y
… | [≤] = let ⟨ m , zs ⟩ = find-min x ys in ⟨ m , y ∷ zs ⟩
… | [>] = let ⟨ m , zs ⟩ = find-min y ys in ⟨ m , x ∷ zs ⟩

-- Selection sort.
--
-- The `TERMINATING` pragma tells Agda to not do a termination check
-- in the definition of `ssort`.  This is OK in this case because the
-- recurion is on `ys`, which will always be a smaller list than `x ∷
-- xs`
{-# TERMINATING #-}
ssort : list ℕ → list ℕ
ssort [] = []
ssort (x ∷ xs) = let ⟨ m , zs ⟩ = find-min x xs in m ∷ ssort zs

-- `x ≤[first] xs` is the proposition that either `xs` is empty, or `x` is
-- less than the first element in `xs`
infix 8 _≤[first]_
data _≤[first]_ (m : ℕ) : list ℕ → Set where
  [] : m ≤[first] []
  ⟨_⟩ : ∀ {n ns}
    → m ≤ n
    → m ≤[first] n ∷ ns

-- `sorted xs` is the proposition that `xs` is sorted
data sorted : list ℕ → Set where
  [] : sorted []
  _∷_ : ∀ {x xs}
    → x ≤[first] xs
    → sorted xs
    → sorted (x ∷ xs)

-- `x ≤[all] ys` is the proposition that `x ≤ y` is true for all
-- elements `y` in `ys`
infix 8 _≤[all]_
data _≤[all]_ (x : ℕ) : list ℕ → Set where
  [] : x ≤[all] []
  _∷_  : ∀ {y : ℕ} {ys : list ℕ}
    → x ≤ y
    → x ≤[all] ys
    → x ≤[all] (y ∷ ys)

---------------
-- EXERCISES --
---------------

-- E1: [★★★]
-- Prove that the min selected from `x ∷ ys` (computed by `find-min x
-- ys`) is less than x.
-- HINTS:
-- ‣ Do induction on `ys`.
-- ‣ Use `xRx[≤]` in the base case.
-- ‣ Do a “with pattern” on `x ≤⋆ y` in the inductive case and then do
--   case analysis on the resulting proof object, giving two
--   subcases. `x ≤⋆ y` gives a proof object that either `x ≤ y` or
--   that `x > y`.
-- ‣ Notice in the goal for each subcase the “(<stuff> | x ≤?
--   y)”. This means that <stuff> will reduce via computation once `x ≤?
--   y` is reduces to a constructor.
-- ‣ In the two subcases under the “with pattern”, do rewrites by
--   `cmp[≤?/≤]` and `cmp[≤?/>]` to reduce the “blocked” term (x ≤? y)
--   in the goal. each of these `cmp[≤?/X]` lemmas take a proof object
--   as argument---use the one you got from the with pattern. After
--   doing this, you should no longer see “(<stuff> | x ≤? y)” in the
--   goal.
-- ‣ After the rewriting by `cmp[≤?/X]`, the first case is by the
--   induction hypothesis, and the second case is by `wk[<]`, `_⊚[≤]_`
--   and the inductive hypothesis. (`wk[<]` weakens a strict ordering
--   `<` to a non-strict ordering `≤` and `_⊚[≤]_` is stransitivity of
--   the non-strict ordering relation `_≤_`.)
find-min-lower-bound-first : ∀ (x : ℕ) (ys : list ℕ) → π₁ (find-min x ys) ≤ x
find-min-lower-bound-first x ys = {!!}

-- E2: [★★★]
-- Prove that the min selected from `x ∷ ys` (computed by `find-min x
-- ys`) is less than the rest of the list (with the min removed).
-- HINTS:
-- ‣ Do induction on `ys`.
-- ‣ Do a with pattern on `x ≤⋆ y` and do case analysis followed by
--   rewrites by `cmp[≤?/X]` (just like in E1).
-- ‣ The very first step of each subcase is to build a proof object of
--   `all` on a cons cell, which is created with `? ∷ ?`, or you can
--   just do “refine” by C-c C-r and Agda will do this for you).
-- ‣ The first subcase is by E1, `_⊚[≤]_` and the inductive
--   hypothesis.
-- ‣ The second subcase is by E1, `_wk[<]_`, `_⊚[≤]_` and the
--   inductive hypothesis.
find-min-lower-bound : ∀ (x : ℕ) (ys : list ℕ) → π₁ (find-min x ys) ≤[all] (π₂ (find-min x ys))
find-min-lower-bound x ys = {!!}

-- E3: [★★☆]
-- Prove that if another value is less than x and less than
-- everythig in ys, then it is less than the min selected from
-- (x ∷ ys).
-- HINTS:
-- ‣ Do induction on `ys`.
-- ‣ Do a with pattern on `x ≤⋆ y` and do case analysis followed by
--   rewrites by `cmp[≤?/X]` (just like in E1 and E2).
-- ‣ Both subcases are by the inductive hypothesis
find-min-upper-bound : ∀ (w x : ℕ) (ys : list ℕ) → w ≤ x → w ≤[all] ys → w ≤ π₁ (find-min x ys)
find-min-upper-bound w x ys εˣ εsʸ = {!!}

-- E4: [★☆☆]
-- Prove that if x is less than every element of ys, then x is less
-- than the first element of the sorted version of ys.
-- HINTS:
-- ‣ Do case analysis on both ys and the proof object of `all (λ y → x ≤
--   y) ys`.
-- ‣ The cons case is by E3
ssort-invariant : ∀ (x : ℕ) (ys : list ℕ) → x ≤[all] ys → x ≤[first] ssort ys
ssort-invariant x ys εs = {!!}

-- E5: [★★☆]
-- Prove that selected sort returns a sorted list.
-- HINTS:
-- ‣ Do induction on xs.
-- ‣ Use the “refine” command as the first step in the inductive case
-- ‣ Use E4 and E2 to construct the proof of `<stuff> ≤[first] <stuff>`.
-- ‣ Assuming the inductive case pattern on the LHS of the equals is
--   `(x ∷ xs)`, the recursive call to `sorted[ssort]` should be
--   exactly:
--
--       sorted[ssort] (π₂ (find-min x xs))
--
--   Agda only allows this recursive call because we have a
--   `TERMINATING` pragma before the proof, which tells Agda to not do
--   termination checks on the recursive call. *If you write
--   `sorted[ssort] (x ∷ xs)` as part of your solution for the
--   inductive case I will mark this as incorrect.*
{-# TERMINATING #-}
sorted[ssort] : ∀ (xs : list ℕ) → sorted (ssort xs)
sorted[ssort] xs = {!!}
