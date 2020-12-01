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

module hw8 where

open import Basics-v4

-- merge sort --

module _ {A : Set} {{_ : has[<?] A}} where
  split : A → A → list A → list A ∧ list A
  split x y [] = ⟨ [ x ] , [ y ] ⟩
  split x y (z ∷ xs) = let ⟨ ys , zs ⟩ = split y z xs in ⟨ x ∷ zs , ys ⟩

  split-length : ∀ (x y : A) (xs : list A) → let ⟨ ys , zs ⟩ = split x y xs
                                              in length ys < length (x ∷ y ∷ xs)
                                               ∧ length zs < length (x ∷ y ∷ xs)
  split-length x y [] = ⟨ Suc Zero , Suc Zero ⟩
  split-length w x (y ∷ xs) with split x y xs | split-length x y xs
  … | ⟨ ys , zs ⟩ | ⟨ IH₁ , IH₂ ⟩ = ⟨ Suc IH₂ , <ᴺ-lmono (length ys) 1 (2 + length xs) IH₁ ⟩

  merge : list A → list A → list A
  merge [] ys = ys
  merge xs [] = xs
  merge (x ∷ xs) (y ∷ ys) with x ≤? y
  … | LE = x ∷ merge xs (y ∷ ys)
  … | GT = y ∷ merge (x ∷ xs) ys

  msort′ : ∀ (xs : list A) → acc _<_ (length xs) → list A
  msort′ [] _ = []
  msort′ [ x ] _ = [ x ]
  msort′ (x ∷ y ∷ xs) (Acc r) =
    let ⟨ ys , zs ⟩ = split x y xs
    in merge (msort′ ys (r (fst (split-length x y xs))))
             (msort′ zs (r (snd (split-length x y xs))))

  msort : list A → list A
  msort xs = msort′ xs (wf (length xs))

-- merge sort permutation verification --

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where

  -- E1: [★]
  -- Prove that `split` returns two lists which in combination are a
  -- permutation of the input.
  -- HINT: do induction on `xs`
  -- HINT: in inductive case, do a combined "with" pattern with both
  --       `split` and `split-perm` (the IH)
  -- HINT: use laws in `cor[+]` for bags, e.g., `+-runit`, `+-assoc`,
  --       `+-commu`
  split-perm : ∀ (x y : A) (xs : list A) →
    let ⟨ ys , zs ⟩ = split x y xs
    in list-elems ys + list-elems zs
     ≡ b[ x ] + b[ y ] + list-elems xs
  split-perm x y xs = {!!}

  -- E2: [★★★]
  -- Prove that `merge-perm` returns a list which is a permutation of
  -- the combination of its arguments.
  -- HINT: do induction on `xs` *and* `ys`
  -- HINT: in the inductive case, do a "with" pattern on the
  --       comparison `≤?` that is blocking evaluation. (No need to
  --       link.)
  -- HINT: use laws in `cor[+]` for bags, e.g., `+-runit`, `+-assoc`,
  --       `+-commu`
  merge-perm : ∀ (xs ys : list A) → list-elems (merge xs ys) ≡ list-elems xs + list-elems ys
  merge-perm [] [] = sym (+-lunit zero)
  merge-perm [] (x₄ ∷ ys) = {!!}
  merge-perm (x₄ ∷ xs) [] = {!!}
  merge-perm (x₄ ∷ xs) (x₅ ∷ ys) = {!!}

  -- E3: [★]
  -- Prove that `msort′` returns a permutation of the input list.
  -- HINT: do case analysis on `xs` and induction on `a` (following
  --       the structure of the implementation of `msort′`). 
  -- HINT: use above two lemmas
  -- HINT: do a combined "with" pattern with each of `split`,
  --       `split-length` and `split-perm`
  -- HINT: use laws in `cor[+]` for bags, e.g., `+-runit`, `+-assoc`,
  --       `+-commu`
  msort′-perm : ∀ (xs : list A) (a : acc _<_ (length xs)) → list-elems (msort′ xs a) ≡ list-elems xs
  msort′-perm [] (Acc x₄) = {!!}
  msort′-perm [ x ] (Acc a) = {!!}
  msort′-perm (x ∷ y ∷ xs) (Acc a) with split x y xs | split-length x y xs | split-perm x y xs
  … | ⟨ ys , zs ⟩ | ⟨ H₁ , H₂ ⟩ | H₃ with msort′-perm ys (a H₁) | msort′-perm zs (a H₂)
  … | IH₁ | IH₂ rewrite merge-perm (msort′ ys (a H₁)) (msort′ zs (a H₂)) = {!most′-perm ys (a H₁)!}
