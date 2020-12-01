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

module hw10 where

open import Basics-v5

syntax vec A n = vec[ n ] A
data vec (A : Set) : ℕ → Set where
  [] : vec[ 0 ] A
  _∷_ : ∀ {n} → A → vec[ n ] A → vec[ Suc n ] A

pattern V[_] a = a ∷ []
pattern V[_,_] a b = a ∷ V[ b ]
pattern V[_,_,_] a b c = a ∷ V[ b , c ]
pattern V[_,_,_,_] a b c d = a ∷ V[ b , c , d ]
pattern V[_,_,_,_,_] a b c d e = a ∷ V[ b , c , d , e ]
pattern V[_,_,_,_,_,_] a b c d e f = a ∷ V[ b , c , d , e , f ]
pattern V[_,_,_,_,_,_,_] a b c d e f g = a ∷ V[ b , c , d , e , f , g ]
pattern V[_,_,_,_,_,_,_,_] a b c d e f g h = a ∷ V[ b , c , d , e , f , g , h ]
pattern V[_,_,_,_,_,_,_,_,_] a b c d e f g h i = a ∷ V[ b , c , d , e , f , g , h , i ]
pattern V[_,_,_,_,_,_,_,_,_,_] a b c d e f g h i j = a ∷ V[ b , c , d , e , f , g , h , i , j ]

matrix[_,_] : ℕ → ℕ → Set → Set
matrix[ m , n ] A = vec[ m ] (vec[ n ] A)

data idx : ℕ → Set where
  Zero : ∀ {n} → idx (Suc n)
  Suc : ∀ {n} → idx n → idx (Suc n)

pattern 𝕟0 = Zero
pattern 𝕟1 = Suc 𝕟0
pattern 𝕟2 = Suc 𝕟1
pattern 𝕟3 = Suc 𝕟2
pattern 𝕟4 = Suc 𝕟3
pattern 𝕟5 = Suc 𝕟4
pattern 𝕟6 = Suc 𝕟5
pattern 𝕟7 = Suc 𝕟6
pattern 𝕟8 = Suc 𝕟7
pattern 𝕟9 = Suc 𝕟8
pattern 𝕟10 = Suc 𝕟9

𝕟 : ∀ (n : ℕ) {m : ℕ} {{_ : n <? m ≡ LT}} → idx m
𝕟 Zero {Zero} ⦃ () ⦄
𝕟 Zero {Suc m} ⦃ ε ⦄ = Zero
𝕟 (Suc n) {Zero} ⦃ () ⦄
𝕟 (Suc n) {Suc m} ⦃ ε ⦄ = Suc (𝕟 n)

_ : let n₁ : idx 20
        n₁ = 𝕟 9
        n₂ : idx 20
        n₂ = 𝕟9
    in n₁ ≡ n₂
_ = refl

pattern I = True
pattern O = False

module _ {A : Set} where

  const[_] : ∀ n → A → vec[ n ] A
  const[ Zero ] x = []
  const[ Suc n ] x = x ∷ const[ n ] x

  _[_] : ∀ {n} → vec[ n ] A → idx n → A
  (x ∷ xs) [ Zero ] = x
  (x ∷ xs) [ Suc ι ] = xs [ ι ]

  _[_↦_] : ∀ {n} → vec[ n ] A → idx n → A → vec[ n ] A
  (x ∷ xs) [ Zero ↦ x′ ] = x′ ∷ xs
  (x ∷ xs) [ Suc ι ↦ x′ ] = x ∷ (xs [ ι ↦ x′ ])

  vec-iter : ∀ {B : Set} {n} → vec[ n ] A → B → (idx n → A → B → B) → B
  vec-iter [] i f = i
  vec-iter (x ∷ xs) i f = vec-iter xs (f Zero x i) λ ι x y → f (Suc ι) x y

-- E1: [★★★]
-- Define the transpose of a matrix. When applied to graphs, this has
-- the effect of reversing all of the edges of the graph.
--
-- You may need to define one or more helper functions.
-- HINT: do induction on `xss` (and use the induction hypothesis)

transpose : ∀ {A : Set} (m n : ℕ) → matrix[ m , n ] A → matrix[ n , m ] A
transpose m n xss = {!!}

-- E2: [★]
-- Write a proposal for your final project. Answer each of these
-- questions below.
{-

1. Team Members. (You may have 1–4.)



2. Algorithm: Identify the algorithm(s) you will consider in the
project. Include any links to webpages or papers that include more
details. There should be a complete description of the algorithm
somewhere for you to use as reference. Try to use the "smallest
possible version of the algorithm" and not a full "practical" version.



3. Specification: Identify the properties of the algorithm(s) that you
will specify.



4. Verification: Identify the techniques from class that you will
apply to approach verification.



5. Library support: Identify which Agda datatypes you will need to
build before you can implement 2, 3 or 4. Indicate which Agda
datatypes which you can axiomatize (as Agda postulates) in order to
get working directly on your problem sooner.



6. Milestones: Identify 2 or 3 key milestones you hope to achieve on
your way to the completion of your full project. Indicate a timeline
for achieving each of these milestones before the final project
presentation deadline Dec 6.



7. Mitigating Risk: Identify a few "backup plans" for how you can
change the trajectory of your final project if one of your milestones
becomes too challenging or unrealistic.



-}

