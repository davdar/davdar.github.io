-- version 2.0

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

module HW7 where

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

-----------------
-- DEFINITIONS --
-----------------

-- well-founded --

data acc (x : ℕ) : Set where
  Acc : (∀ {y} → y < x → acc y) → acc x

acc[<] : ∀ {m} (n : ℕ) → m < n → acc m
acc[<] Z ()
acc[<] (S n) Z = Acc λ where ()
acc[<] (S n) (S ε) = Acc λ where ε′ → (acc[<] n) ( to[</≤] ε ⊚[≤/<] ε′)

wf[<] : ∀ (n : ℕ) → acc n
wf[<] n = Acc (acc[<] n)

---------------
-- EXERCISES --
---------------

-- merge sort --

split : list ℕ → list ℕ ∧ list ℕ
split [] = ⟨ [] , [] ⟩
split (x ∷ xs) = let ⟨ ys , zs ⟩ = split xs in ⟨ zs , x ∷ ys ⟩

merge : list ℕ → list ℕ → list ℕ
merge [] ys = ys
merge xs [] = xs
merge (x ∷ xs) (y ∷ ys) with x ≤? y
… | [≤] = x ∷ merge xs (y ∷ ys)
… | [>] = y ∷ merge (x ∷ xs) ys

-- E1: [★★☆]
-- Prove that if you split a list, the resulting lists are of equal or
-- smaller length than the starting list.
-- HINTS:
-- ‣ do induction on xs
-- ‣ use “refine” (C-c C-r) to get started on the goal
-- ‣ in the recursive case, use a with pattern to name and then do
--   case analysis (C-c C-c) on the inductive hypothesis
-- ‣ use _⊚[≤]_ and s[≤]
split-length : ∀ (xs : list ℕ) → let ⟨ ys , zs ⟩ = split xs in length ys ≤ length xs ∧ length zs ≤ length xs
split-length xs = {!!}

msort-rec : ∀ (xs : list ℕ) → acc (length xs) → list ℕ
msort-rec [] a = []
msort-rec [ x ] a = [ x ]
msort-rec (x₁ ∷ x₂ ∷ xs) (Acc a) with split xs | split-length xs
… | ⟨ ys , zs ⟩ | ⟨ H₁ , H₂ ⟩ =
  merge (msort-rec (x₁ ∷ ys) (a (S (s[<] (length xs) ⊚[</≤] H₁))))
        (msort-rec (x₂ ∷ zs) (a (S (s[<] (length xs) ⊚[</≤] H₂))))

msort : list ℕ → list ℕ
msort xs = msort-rec xs (wf[<] (length xs))

-- E2: [★★☆]
-- Prove that if an element is smaller than the head of two lists,
-- then that element is also smaller than the merge of those lists.
-- HINTS:
-- ‣ do induction on ys and zs
-- ‣ in the last case (both cons cells): do case analysis on both
--   proof objects of _≤[first]_, then do a with pattern on `y ≤? z`
--   (assuming you renamed the first element in `ys` to be `y` and
--   likewise for `zs`)
merge-bounded : ∀ (x : ℕ) (ys zs : list ℕ) → x ≤[first] ys → x ≤[first] zs → x ≤[first] (merge ys zs)
merge-bounded x ys zs ε₁ ε₂ = {!!}

-- E3: [★★★]
-- Prove that if two lists are sorted, then their merge is sorted.
-- HINTS:
-- ‣ do induction on xs and ys, and then case analysis on εs₁ and εs₂;
--   you can do this at once by typing `xs ys εs₁ εs₂` in the hole and
--   then one case analysis command
-- ‣ in the last case (both cons cells), do a with pattern on `x ≤⋆ y`
--   and use rewrite in the two subcases using cmp[≤?/≤] and cmp[≤?/>]
-- ‣ use wk[<] and E2
merge-sorted : ∀ (xs ys : list ℕ) → sorted xs → sorted ys → sorted (merge xs ys)
merge-sorted xs ys εs₁ εs₂ = {!!}

-- E4: [★★★]
-- Prove that the recursively defined version of merge sort results
-- in a sorted list
-- HINTS:
-- ‣ do induction on xs by doing case analysis “C-c C-c” *twice*; this
--   will give cases for the empty list, the singleton list, and a
--   list with at least two elements. (`msort-rec` is defined in this
--   way with three cases.)
-- ‣ in the recursive case, do case analysis on `a`, the accessibility proof object
-- ‣ in the recursive case, do a with pattern on `split xs` and
--   `split-length xs` (separated by a `|`), and then do case analysis
--   on each (they are both pairs)
-- ‣ use E3 and the inductive hypothesis (i.e., the recursive call to
--   `msort-sorted-rec`)
-- ‣ in the recursive call to `msort-sorted-rec`, you are allowed to
--   use `a <anything>` as the accessibility proof of the recursive
--   call
-- ‣ the proof object you need to give to `a` is a proof of
--   ordering; it will be the same proof object that is used in the
--   definition of `msort-rec`.
msort-sorted-rec : ∀ (xs : list ℕ) (a : acc (length xs)) → sorted (msort-rec xs a)
msort-sorted-rec xs a = {!!}

-- E5: [★☆☆]
-- Prove that merge sort results in a sorted list.
-- HINTS:
-- ‣ do *not* do induction or case analysis
-- ‣ use E4 and wf[<]
msort-sorted : ∀ (xs : list ℕ) → sorted (msort xs)
msort-sorted xs = {!!}
