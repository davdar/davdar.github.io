module ic18 where

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
balance-tall t₁ x t₂ κ = {!!}

postulate
  push : ∀ {m} → ℕ → tree m → extree

postulate
  locate : ∀ {m n} → ℕ → tree n → context m n → context m Zero

insert : ∀ {m} → ℕ → tree m → extree
insert x t = {!!}

postulate
  balance-short : ∀ {m n} → tree n → context m (Suc n) → extree

pop : ∀ {m} → tree m → option (ℕ ∧ extree)
pop t = {!!}

-- final project ideas:

{-

⁃ greatest common divisor (GCD)  
  [https://en.wikipedia.org/wiki/Greatest_common_divisor]
⁃ finger trees                   
  [https://en.wikipedia.org/wiki/Finger_tree]
  [https://www.cs.ox.ac.uk/ralf.hinze/publications/FingerTrees.pdf]
⁃ (graphs) 
  topological sort
  eulerian circuit
  minimum spanning tree
  strongly connected components
  [https://web.stanford.edu/class/cs97si/06-basic-graph-algorithms.pdf]
⁃ boolean satisfiability (SAT)
  [https://en.wikipedia.org/wiki/Boolean_satisfiability_problem]
  [http://andrew.gibiansky.com/blog/verification/writing-a-sat-solver/]
⁃ regex and parsing
  [https://en.wikipedia.org/wiki/Brzozowski_derivative]
  [https://gallais.github.io/pdf/agdarsec18.pdf]
⁃ small compiler
  [http://adam.chlipala.net/cpdt/cpdt.pdf] (Chapter 2)

-}
