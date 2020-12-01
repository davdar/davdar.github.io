{-
Name: ⁇
Date: ⁇

Collaboration Statement:
«Write your collaboration statement here…»
-}

---------------
-- LOGISTICS --
---------------

-- To submit the assignment, upload your solution to blackboard as a
-- single .agda file.
--
-- Make sure you write your name, the date, and your collaboration
-- statement above, as indicated by the course course collaboration
-- policy:
--
--     Collaboration on the high-level ideas and approach on
--     assignments is encouraged. Copying someone else's work is not
--     allowed. Any collaboration, even at a high level, must be
--     declared when you submit your assignment. Every assignment must
--     include a collaboration statement. E.g., "I discussed
--     high-level strategies for solving problem 2 and 5 with Alex."
--     Students caught copying work are eligible for immediate failure
--     of the course and disciplinary action by the University. All
--     academic integrity misconduct will be treated according to
--     UVM's Code of Academic Integrity.
--
-- This assignment consists of a LIB section which contains relevant
-- definitions and lemmas which you should refer to throughout the
-- assignment, and an ASSIGNMENT section which contains definitions
-- and lemmas with “holes” in them. *If you only change the code
-- within the holes and your entire assignment compiles without
-- errors, you are guaranteed 100% on the assignment.*

module hw9 where

open import Basics-v4

data tree : ℕ → Set where
  L : tree 0
  2[_<_>_] : ∀ {n} → tree n → ℕ → tree n → tree (Suc n)
  3[_<_>_<_>_] : ∀ {n} → tree n → ℕ → tree n → ℕ → tree n → tree (Suc n)

t1 : tree 2
t1 = 3[ 2[ L < 1 > L ] < 2 > 3[ L < 3 > L < 4 > L ] < 5 > 2[ L < 6 > L ] ]

data context (m : ℕ) : ℕ → Set where
  T : context m m
  2[X<_>_/_] : ∀ {n} → ℕ → tree n → context m (Suc n) → context m n
  2[_<_>X/_] : ∀ {n} → tree n → ℕ → context m (Suc n) → context m n
  3[X<_>_<_>_/_] : ∀ {n} → ℕ → tree n → ℕ → tree n → context m (Suc n) → context m n
  3[_<_>X<_>_/_] : ∀ {n} → tree n → ℕ → ℕ → tree n → context m (Suc n) → context m n
  3[_<_>_<_>X/_] : ∀ {n} → tree n → ℕ → tree n → ℕ → context m (Suc n) → context m n

zip : ∀ {m n} → tree n → context m n → tree m
zip t T = t
zip t₁ 2[X< x > t₂ / κ ] = zip 2[ t₁ < x > t₂ ] κ
zip t₂ 2[ t₁ < x >X/ κ ] = zip 2[ t₁ < x > t₂ ] κ
zip t₁ 3[X< x₁ > t₂ < x₂ > t₃ / κ ] = zip 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ
zip t₂ 3[ t₁ < x₁ >X< x₂ > t₃ / κ ] = zip 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ
zip t₃ 3[ t₁ < x₁ > t₂ < x₂ >X/ κ ] = zip 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ

first-context : ∀ {m n} → tree n → context m n → context m Zero
first-context L κ = κ
first-context 2[ t₁ < x > t₂ ] κ = first-context t₁ 2[X< x > t₂ / κ ]
first-context 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ = first-context t₁ 3[X< x₁ > t₂ < x₂ > t₃ / κ ]

data extree : Set where
  Ex : ∀ {m} → tree m → extree

balance-tall : ∀ {m n} → tree n → ℕ → tree n → context m n → extree
balance-tall t₁ x t₂ T = Ex 2[ t₁ < x > t₂ ]
balance-tall t₁ x₁ t₂ 2[X< x₂ > t₃ / κ ] = Ex (zip 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ) 
balance-tall t₂ x₂ t₃ 2[ t₁ < x₁ >X/ κ ] = Ex (zip 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ) 
balance-tall t₁ x₁ t₂ 3[X< x₂ > t₃ < x₃ > t₄ / κ ] = balance-tall 2[ t₁ < x₁ > t₂ ] x₂ 2[ t₃ < x₃ > t₄ ] κ
balance-tall t₂ x₂ t₃ 3[ t₁ < x₁ >X< x₃ > t₄ / κ ] = balance-tall 2[ t₁ < x₁ > t₂ ] x₂ 2[ t₃ < x₃ > t₄ ] κ
balance-tall t₃ x₃ t₄ 3[ t₁ < x₁ > t₂ < x₂ >X/ κ ] = balance-tall 2[ t₁ < x₁ > t₂ ] x₂ 2[ t₃ < x₃ > t₄ ] κ

-- E1: [★]
-- implement push which inserts a value into the front of the tree
-- HINT: do not use recursion; use first-context and balance-tall
push : ∀ {m} → ℕ → tree m → extree
push n t = {!!}

_ : push 2 2[ L < 1 > L ] ≡ Ex 3[ L < 2 > L < 1 > L ]
_ = refl

_ : push 3 3[ L < 2 > L < 1 > L ] ≡ Ex 2[ 2[ L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
_ = refl

_ : push 4 2[ 2[ L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
    ≡ Ex 2[ 3[ L < 4 > L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
_ = refl

_ : push 5 2[ 3[ L < 4 > L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
    ≡ Ex 3[ 2[ L < 5 > L ] < 4 > 2[ L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
_ = refl

_ : push 6 3[ 2[ L < 5 > L ] < 4 > 2[ L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
    ≡ Ex 3[ 3[ L < 6 > L < 5 > L ] < 4 > 2[ L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
_ = refl

-- E2: [★★]
-- implement locate which locates the place to insert a value in a
-- tree of sorted values
-- HINT: do recursion on t; use comparison ≤? or ∇? and first-context

locate : ∀ {m n} → ℕ → tree n → context m n → context m Zero
locate n t κ = {!!}

_ : locate 15 2[ 2[ L < 10 > L ] < 20 > 2[ L < 30 > L ] ] T ≡ 2[ L < 10 >X/ 2[X< 20 > 2[ L < 30 > L ] / T ] ]
_ = refl

_ : locate 25 2[ 2[ L < 10 > L ] < 20 > 2[ L < 30 > L ] ] T ≡ 2[X< 30 > L / 2[ 2[ L < 10 > L ] < 20 >X/ T ] ]
_ = refl

_ : locate 15 3[ 3[ L < 10 > L < 20 > L ] < 30 > 2[ L < 40 > L ] < 50 > 2[ L < 60 > L ] ] T
    ≡ 3[ L < 10 >X< 20 > L / 3[X< 30 > 2[ L < 40 > L ] < 50 > 2[ L < 60 > L ] / T ] ]
_ = refl

_ : locate 25 3[ 3[ L < 10 > L < 20 > L ] < 30 > 2[ L < 40 > L ] < 50 > 2[ L < 60 > L ] ] T
    ≡ 3[ L < 10 > L < 20 >X/ 3[X< 30 > 2[ L < 40 > L ] < 50 > 2[ L < 60 > L ] / T ] ]
_ = refl

_ : locate 35 3[ 3[ L < 10 > L < 20 > L ] < 30 > 2[ L < 40 > L ] < 50 > 2[ L < 60 > L ] ] T
    ≡ 2[X< 40 > L / 3[ 3[ L < 10 > L < 20 > L ] < 30 >X< 50 > 2[ L < 60 > L ] / T ] ]
_ = refl

insert : ∀ {m} → ℕ → tree m → extree
insert x t =
  let κ = locate x t T
  in balance-tall L x L κ

-- E3: [★★★]
-- implement balance-short which places a tree which is one-too-small
-- into a context by balancing and rotating
-- HINT: do recursion on κ; use balance-tall for inspiration

balance-short : ∀ {m n} → tree n → context m (Suc n) → extree
balance-short t T = {!!}
balance-short t₁ 2[X< x₁ > 2[ t₂ < x₂ > t₃ ] / κ ] = balance-short 3[ t₁ < x₁ > t₂ < x₂ > t₃ ] κ
balance-short t₁ 2[X< x > 3[ t₂ < x₁ > t₃ < x₂ > t₄ ] / κ ] = Ex (zip {!!} κ)
balance-short t 2[ x < x₁ >X/ κ ] = {!!}
balance-short t 3[X< x > x₁ < x₂ > x₃ / κ ] = {!!}
balance-short t 3[ x < x₁ >X< x₂ > x₃ / κ ] = {!!}
balance-short t 3[ x < x₁ > x₂ < x₃ >X/ κ ] = {!!}

pop : ∀ {m} → tree m → option (ℕ ∧ extree)
pop t with first-context t T
pop t | T = None
pop t | 2[X< x > L / κ ] = Some ⟨ x , balance-short L κ ⟩
pop t | 2[ L < x >X/ κ ] = Some ⟨ x , balance-short L κ ⟩
pop t | 3[X< x₁ > L < x₂ > L / κ ] = Some ⟨ x₁ , Ex (zip 2[ L < x₂ > L ] κ) ⟩
pop t | 3[ L < x₁ >X< x₂ > L / κ ] = Some ⟨ x₁ , Ex (zip 2[ L < x₂ > L ] κ) ⟩
pop t | 3[ L < x₁ > L < x₂ >X/ κ ] = Some ⟨ x₁ , Ex (zip 2[ L < x₂ > L ] κ) ⟩

_ : pop 2[ 2[ L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
    ≡ Some ⟨ 3 , Ex 3[ L < 2 > L < 1 > L ] ⟩
_ = refl

_ : pop 2[ 3[ L < 4 > L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
    ≡ Some ⟨ 4 , Ex 2[ 2[ L < 3 > L ] < 2 > 2[ L < 1 > L ] ] ⟩
_ = refl

_ : pop 3[ 2[ L < 5 > L ] < 4 > 2[ L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
    ≡ Some ⟨ 5 , Ex 2[ 3[ L < 4 > L < 3 > L ] < 2 > 2[ L < 1 > L ] ] ⟩
_ = refl

_ : pop 3[ 3[ L < 6 > L < 5 > L ] < 4 > 2[ L < 3 > L ] < 2 > 2[ L < 1 > L ] ]
    ≡ Some ⟨ 6 , Ex 3[ 2[ L < 5 > L ] < 4 > 2[ L < 3 > L ] < 2 > 2[ L < 1 > L ] ] ⟩
_ = refl

-- E4: [★]
-- Start searching for final project ideas. Write three potential
-- final project algorithms or data structures which you might choose
-- as a final project. For each final project idea, write the property
-- that you would verify. You will only need to pick one project
-- topic, and you are not restricted to pick one of these three—these
-- are just initial ideas to get started.

{-
Project 1:  

<write here>

Properties to verify:

<write here>

Project 2:

<write here>

Properties to verify:

<write here>

Project 3:

<write here>

Properties to verify:

<write here>

-}
