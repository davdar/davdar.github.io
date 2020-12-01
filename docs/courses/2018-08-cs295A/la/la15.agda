module la15 where

open import Basics-v3

--------------
-- IN CLASS --
--------------

-- permutation as a spec --

data perm {A : Set} : list A → list A → Set where
  [] : perm [] []
  Skip : ∀ {x : A} {xs ys : list A}
    → perm xs ys
    → perm (x ∷ xs) (x ∷ ys)
  Swap : ∀ {x y : A} {xs ys : list A}
    → perm xs ys
    → perm (x ∷ y ∷ xs) (y ∷ x ∷ xs)
  Trans : ∀ {xs ys zs : list A}
    → perm xs ys
    → perm ys zs
    → perm xs zs

_ : perm [ 1 , 2 , 3 ] [ 3 , 2 , 1 ]
_ = Trans (Skip (Swap [])) (Trans (Swap (Skip [])) (Skip (Swap [])))

module Doesn't-Work where
  ¬Perm : ¬ perm [ 1 , 1 , 2 ] [ 1 , 2 , 2 ]
  ¬Perm = {!!}

-- -------------------------- --
-- tour of multiset in Basics --
-- -------------------------- --

_ : ¬ list-elems [ 1 , 1 , 2 ] ≡ list-elems [ 1 , 2 , 2 ]
_ rewrite unblock = λ ()

-- permutation for selection sort --

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where
  find-min : A → list A → A ∧ list A
  find-min x [] = ⟨ x , [] ⟩
  find-min x (y ∷ xs) with x ≤? y
  … | LE = let ⟨ m , ys ⟩ = find-min x xs in ⟨ m , y ∷ ys ⟩
  … | GT = let ⟨ m , ys ⟩ = find-min y xs in ⟨ m , x ∷ ys ⟩

  find-min-length : ∀ (y : A) (xs : list A) → let ⟨ m , xs′ ⟩ = find-min y xs in length xs ≡ length xs′
  find-min-length y [] = refl
  find-min-length y (x ∷ xs) with y ≤? x
  … | LE rewrite find-min-length y xs = refl
  … | GT rewrite find-min-length x xs = refl

  find-min-perm : ∀ (x : A) (xs : list A) → let ⟨ m , ys ⟩ = find-min x xs in b[ m ] + list-elems ys ≡ b[ x ] + list-elems xs
  find-min-perm x [] = refl
  find-min-perm x (y ∷ xs) with x ≤? y
  find-min-perm x (y ∷ xs) | LE with find-min x xs | find-min-perm x xs
  … | ⟨ m , ys ⟩ | IH
    rewrite +-commu b[ y ] (list-elems ys)
          | +-commu b[ y ] (list-elems xs)
          | +-assoc b[ m ] (list-elems ys) b[ y ]
          | +-assoc b[ x ] (list-elems xs) b[ y ]
          | IH 
          = refl
  find-min-perm x (y ∷ xs) | GT with find-min y xs | find-min-perm y xs
  … | ⟨ m , ys ⟩ | IH
    rewrite +-assoc b[ m ] b[ x ] (list-elems ys)
          | +-commu b[ m ] b[ x ]
          | sym (+-assoc b[ x ] b[ m ] (list-elems ys))
          | IH
          = refl

  ssort′ : ∀ (xs : list A) → acc _<_ (length xs) → list A
  ssort′ [] _ = []
  ssort′ (x ∷ xs) (Acc r) with find-min x xs | find-min-length x xs
  … | ⟨ m , ys ⟩ | H = m ∷ ssort′ ys (r (≤-to-< (≤-refl-≡ _ _ (sym H))))

  ssort : ∀ (xs : list A) → list A
  ssort xs = ssort′ xs (wf (length xs))

  ssort′-perm : ∀ (xs : list A) (ε : acc _<_ (length xs)) → list-elems (ssort′ xs ε) ≡ list-elems xs
  ssort′-perm [] _ = refl
  ssort′-perm (x ∷ xs) (Acc r) with find-min x xs | find-min-length x xs | find-min-perm x xs
  … | ⟨ m , ys ⟩ | H₁ | H₂ rewrite ssort′-perm ys (r (≤-to-< (≤-refl-≡ _ _ (sym H₁)))) = H₂

  ssort-perm : ∀ (xs : list A) → list-elems (ssort xs) ≡ list-elems xs
  ssort-perm xs = ssort′-perm xs (wf (length xs))

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

_ : split 1 2 [ 3 , 4 , 5 , 6 ] ≡ ⟨ [ 1 , 3 , 5 ] , [ 2 , 4 , 6 ] ⟩
_ = refl

_ : msort [ 4 , 2 , 1 , 3 ]  ≡ [ 1 , 2 , 3 , 4 ]
_ = refl

-- next homework --

module _ {A : Set} {{_ : has[<] A}} {{_ : cor[<] A}} {{_ : has[<?] A}} {{_ : cor[<?] A}} where
  postulate
    split-perm : ∀ (x y : A) (xs : list A) →
      let ⟨ ys , zs ⟩ = split x y xs
      in list-elems ys + list-elems zs
       ≡ b[ x ] + b[ y ] + list-elems xs

    merge-perm : ∀ (xs ys : list A) → list-elems (merge xs ys) ≡ list-elems xs + list-elems ys

    msort′-perm : ∀ (xs : list A) (a : acc _<_ (length xs)) → list-elems (msort′ xs a) ≡ list-elems xs
