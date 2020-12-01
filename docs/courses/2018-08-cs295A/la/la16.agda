module la16 where

open import Basics-v4

data color : Set where
  R : color
  B : color

data rbt : Set where
  Leaf : rbt
  [_/_/_] : color → rbt → rbt → rbt

t0 : rbt
t0 = [ R / Leaf / Leaf ]

-- the number of black nodes from every leaf to the root
data black-nodes : rbt → ℕ → Set where
  Leaf : black-nodes Leaf 1
  Node-R : ∀ {n t₁ t₂}
    → black-nodes t₁ n
    → black-nodes t₂ n
    → black-nodes [ R / t₁ / t₂ ] n
  Node-B : ∀ {n t₁ t₂}
    → black-nodes t₁ n
    → black-nodes t₂ n
    → black-nodes [ B / t₁ / t₂ ] (Suc n)

data is-black : rbt → Set where
  Leaf : is-black Leaf
  Node : ∀ {t₁ t₂}
    → is-black [ B / t₁ / t₂ ]

-- every red node has black (not red) children
data red-children : rbt → Set where
  Leaf : red-children Leaf
  Node-R : ∀ {t₁ t₂}
    → is-black t₁
    → is-black t₂
    → red-children [ R / t₁ / t₂ ]
  Node-B : ∀ {t₁ t₂}
    → red-children [ B / t₁ / t₂ ]
  

t1 : rbt
t1 = [ R / [ B / Leaf / Leaf ]
            / [ B / [ R / Leaf / Leaf ]
                     / Leaf ] ]

_ : black-nodes t1 2
_ = Node-R (Node-B Leaf Leaf) (Node-B (Node-R Leaf Leaf) Leaf)

_ : red-children t1
_ = Node-R Node Node

_ : black-nodes t1 2 ∧ red-children t1
_ = ⟨ Node-R (Node-B Leaf Leaf) (Node-B (Node-R Leaf Leaf) Leaf) ,
      Node-R Node Node ⟩

t2 : rbt
t2 = [ B / [ R / [ R / Leaf / Leaf ]
                     / Leaf ]
            / Leaf ]

_ : black-nodes t2 2
_ = Node-B (Node-R (Node-R Leaf Leaf) Leaf) Leaf

_ : red-children t2
_ = Node-B

_ : black-nodes t2 2 ∧ red-children t2
_ = ⟨ Node-B (Node-R (Node-R Leaf Leaf) Leaf) Leaf , Node-B ⟩
