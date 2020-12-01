-- [Nearly all of this material is borrowed from [plfa.Naturals]
-- authored by Wen Kokke and Philip Wadler.]
-- 
-- [plfa.Naturals]: https://plfa.github.io/Naturals/
-- 
-- # Naturals
-- 
-- First we declare that this is a module named `la3`. The module name
-- *must* be the same as the file name.

module la3 where

-- Now, load this file by typing `C-c C-l`.
-- 
-- **COMMAND: `C-c C-l` is for "load".**
-- 
-- What follows is a small library. Let's skip it for now.

-------------
-- LIBRARY --
-------------

infix 1 begin_
infixr 2 _is-≡_
infix 3 _∎
infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

begin_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
begin x≡y = x≡y

_is-≡_ : ∀ {A : Set} (x : A) {y : A} → x ≡ y → x ≡ y
_ is-≡ x≡y = x≡y

_∎ : ∀ {A : Set} (x : A) → x ≡ x
_ ∎ = refl

--------------
-- IN CLASS --
--------------

-- # Natural Numbers
-- 
-- Here is an inductive definition of natural numbers in “math world”:
-- 
--     --------
--     zero : ℕ
-- 
--     m : ℕ
--     ---------
--     suc m : ℕ
-- 
-- here is an inductive definition of natural numbers in Agda:

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- This definition says:
-- 
-- - `data ℕ` means we are defining `ℕ` inductively (as in math above)
-- - `ℕ : Set` means `ℕ` is a set, so we are defining a set inductively
-- - `zero : ℕ` says that `zero` is in the set `ℕ`
-- - `suc : ℕ → ℕ` says that `suc(n)` is in the set `ℕ` when `n` is in
--    the set `ℕ`.
-- 
-- If we were to annotate the definition with its math analog, we would
-- write:

data ℕ′ : Set where
  -- --------
  -- zero : ℕ

  zero : ℕ′

  -- m : ℕ
  -- ---------
  -- suc m : ℕ

  suc : ℕ′ → ℕ′

-- There are two fancy input characters here: `ℕ` and `→`.
-- 
-- - To write `ℕ` type `\bn`.
-- - To write `→` type `\r`.
-- 
-- If you ever want to know the input code for a unicode character that
-- is displayed, put the cursor over the character and type `C-u C-x =`
-- or `M-1 C-x =`. (Try it out.)
-- 
-- **COMMAND: `C-u C-x =` and `M-1 C-x =` are for "how do I type this?".**
-- 
-- These commands use "agda input mode" which is enabled by default when
-- editting .agda or .lagda files. (This is a .lagda file, which stands
-- for "literate agda". Literate agda files are text first, and you write
-- code in explicit code blocks, as opposed to being code first, and
-- where you write text in explicit comment blocks.)
-- 
-- Let's play around with emacs mode for a bit...
-- 
-- Put your cursor somewhere in this paragraph and type `C-c C-f`. It
-- should jump the cursor inside the hole. Do the command again; it
-- should jump the cursor into the next hole. `Type C-c C-b`. It should
-- jump the cursor back to the hole above.
-- 
-- **COMMAND: `C-c C-f` is for "forward" and `C-c C-b` is for "back".**

e-one : ℕ
e-one = suc zero

_ : e-one ≡ 1
_ = refl

-- Put the cursor inside the hole and type `C-c C-,`. This should tell
-- you that the goal is `ℕ`. Write `suc` into the hole and type `C-c
-- C-.`. This should tell you that the goal is `ℕ`, but what you have
-- (`suc`) is `ℕ → ℕ`.
-- 
-- **COMMAND: `C-c C-,` is for "what is the goal?".**
-- 
-- **COMMAND: `C-c C-.` is for "what is in the hole?".**
-- 
-- Keep your cursor in the hole and type `C-c C-SPC` (`SPC` =
-- space). This should tell you that `suc` isn't the right type.
-- It tells you this in two ways:
-- 
--     ℕ → ℕ !=< ℕ
--       ^       ^─── the goal
--       ╰─── what's in the hole
-- 
-- This is Agda's way of saying that functions between natrual numbers
-- are not the same as natural numbers.
-- 
-- > when checking that the expression suc has type ℕ
-- 
-- This is Agda's way of reminding you what is in the hole, and what its
-- type is *supposed* to be.
-- 
-- Keep your cursor in the hole and type `C-c C-r`. This should succeed,
-- and create a new hole as the argument to `suc`.
-- 
-- **COMMAND: `C-c C-SPC` is for "this is the answer"**
-- 
-- **COMMAND: `C-c C-r is for "refine", i.e., "here is a partial answer"**
-- 
-- Go to the new hole and type `zero` and then `C-c C-SPC`.
-- 
-- Exercise: fill in these definitions:

e-zero : ℕ
e-zero = zero

e-two : ℕ
e-two = suc (suc zero)

e-three : ℕ
e-three = suc (suc (suc zero))

_ : e-zero ≡ 0
_ = refl
_ : e-three ≡ 3
_ = refl

-- You can use old definitions to create new ones. Define `e-three` again
-- but this time use `e-two` as part of its definition:

e-three′ : ℕ
e-three′ = suc e-two

-- ## Plus
-- 
-- Let's define it together. First, notice that `_+_` takes two
-- arguments. In the definition of `+`, we get to write the arguments
-- "around" the operator (called "infix"). This is because Agda knows
-- that when functions are declared with underscores in their name, those
-- are placeholders for argument positions. Notationally:
-- 
--     _+_ m n
-- 
-- and
-- 
--     m + n
-- 
-- are always equivalent *syntacically*.

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- **Aside:** First, note the type of `+` which is `ℕ → ℕ → ℕ`. In the
-- usual mathematical notation, a two-argument operation is written `ℕ ×
-- ℕ → ℕ`, where `×` here is cartesian product for sets. In Agda we will
-- write two argument functions instead as `ℕ → ℕ → ℕ`. This type is
-- technically parsed as `ℕ → (ℕ → ℕ)`, that is "give me a number, and
-- I'll give you back a function that takes a number and returns a
-- number."  A call to `+` (in prefix style) is `_+_ m n` which is
-- technically parsed `(_+_ m) n`, that is, "first apply to m, then take
-- the function that is returned and apply n". This idea generalizes to
-- any number of arguments and is much lighter weight syntactically than
-- being explicit about how many arguments something takes in the syntax
-- of application.
-- 
-- We are going to define `+` on natural numbers by induction on the
-- first operand. Put the cursor inside of the hole and write `m`. Then
-- type `C-c C-c`. This will "case split" `m` into its two cases: `m` is
-- either `zero`, or the successor of some other number `m`.
-- 
-- We must now define plus for these two cases. The `zero` case is
-- easy. What do we do in the `suc` case? The principle of induction says
-- we are allowed to call `+` inside the definition of `+`, so long as
-- it's on a strictly smaller number than *this* call to `+`. Inside that
-- hole, write `suc (m + n)` and ask Agda to fill the hole with it.
-- 
-- It is worth noting there that `suc` is not an operation—it is
-- *data*. `2` and `suc (suc zero)` are exactly the same thing. `suc (suc
-- zero)` doesn't *compute* `2`, it *is* `2`. `+` on the other hand is an
-- *operation*. `+` is creating a new number by tearing apart the
-- representation of the first number.
-- 
-- Let's take a look at how Agda computes `2 + 3`. The following is
-- technically a *proof* that `2 + 3 ≡ 5`, and we will use small proof
-- steps to explore Agda's thinking.
-- 
-- (Note that we write `=` for defining things and `≡` for the
-- proposition that two things are equal. On paper (or the blackboard) we
-- write `≜` for defining things and `=` for the proposition that two
-- things are equal.)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  is-≡    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  is-≡    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  is-≡    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  is-≡    -- base case
    suc (suc (suc (suc (suc zero))))
  is-≡    -- is longhand for
    5
  ∎

-- Any line of reasoning that follows direcly from the rules of
-- computation (given by the definition of functions like `+`) is
-- performed *automatically* by Agda. Because the fact that `2 + 3 ≡ 5`
-- follows directly by computation, Agda is also happy with the following
-- proof.

_ : 2 + 3 ≡ 5
_ = refl

-- The proof object here is `refl` which stands for
-- "reflexivity". Reflexivity is technically a proof that `x ≡ x` for any
-- `x`. So how were we able to use this proof object to prove `2 + 3 ≡
-- 5`? This is because in terms of provability, all proofs are
-- interpreted *modulo computation*. Because `2 + 3` *computes* to `5`,
-- the proof object `refl : 5 ≡ 5` is perfectly good for proving `2 + 3 ≡
-- 5`.
-- 
-- ## Times
-- 
-- Let's define multiplication now.

_*_ : ℕ → ℕ → ℕ
zero * n     =  zero
(suc m) * n  =  n + (m * n)

-- Let's walk through how Agda multiplies two and three.

_ =
  begin
    2 * 3
  is-≡    -- inductive case
    3 + (1 * 3)
  is-≡    -- inductive case
    3 + (3 + (0 * 3))
  is-≡    -- base case
    3 + (3 + 0)
  is-≡    -- simplify
    6
  ∎

-- ## Monus
-- 
-- Let's define subtraction. Because we don't have negative natural
-- numbers (we just haven't defined them yet) we are going to say `m ∸ n
-- = 0` when `n > m`

_∸_ : ℕ → ℕ → ℕ
m       ∸ zero     =  m
zero    ∸ n        =  zero
(suc m) ∸ (suc n)  =  m ∸ n

-- Agda knows that we have covered all the cases. If we hadn't it would
-- complain. (Try it out.)
-- 
-- Let's walk through how Agda subtracts 2 from 3.

_ =
  begin
     3 ∸ 2
  is-≡
     2 ∸ 1
  is-≡
     1 ∸ 0
  is-≡
     1
  ∎

-- and how Agda subtracts 3 from 2.

_ =
  begin
     2 ∸ 3
  is-≡
     1 ∸ 2
  is-≡
     0 ∸ 1
  is-≡
     0
  ∎

-- Notationally, we typically want to interpret `1 + 2 * 3` as `1 + (2 *
-- 3)` and *not* `(1 + 2) * 3`. We can tell agda the *precedence* of
-- these operations as follows:

infixl 6  _+_  _∸_
infixl 7  _*_

_ : 1 + 2 * 3 ∸ 7 ≡ 0
_ = refl

-- ## Efficient Nats
-- 
-- The representation of `ℕ` above is inefficient. Addition is an O(N)
-- operation, whereas an efficient implementation of addition (for
-- unbounded natural numbers) should be O(㏒(N)).
-- 
-- Here is the efficient representation:

data bin-ℕ : Set where
  bits : bin-ℕ
  _x0 : bin-ℕ → bin-ℕ
  _x1 : bin-ℕ → bin-ℕ

-- For instance, the bitstring
-- 
--     1011
-- 
-- standing for the number eleven is encoded as:
-- 
--     bits x1 x0 x1 x1
-- 
-- Representations are not unique due to leading zeros.
-- Hence, eleven is also represented by `001011`, encoded as
-- 
--     x0 x0 x1 x0 x1 x1 nil
-- 
-- Exercise: Define a successor function and plus:

inc : bin-ℕ → bin-ℕ
inc bits = bits x1
inc (n x0) = n x1
inc (n x1) = (inc n) x0

_ : inc (bits x1 x0 x1 x1) ≡ bits x1 x1 x0 x0
_ = refl

infixl 6  _bin-+_
_bin-+_ : bin-ℕ → bin-ℕ → bin-ℕ
bits bin-+ n = n
m bin-+ bits = m
(m x0) bin-+ (n x0) = (m bin-+ n) x0
(m x0) bin-+ (n x1) = (m bin-+ n) x1
(m x1) bin-+ (n x0) = (m bin-+ n) x1
(m x1) bin-+ (n x1) = inc ((m bin-+ n) x1)

_ : bits x1 x0 x1 x1 bin-+ bits x1 x0 x1 x0 ≡ bits x1 x0 x1 x0 x1
_ = refl

-- Exercise: Define a to and from function:

to : ℕ → bin-ℕ
to zero = bits
to (suc n) = inc (to n)

from : bin-ℕ → ℕ
from bits = 0
from (n x0) = 2 * from n
from (n x1) = 2 * from n + 1

_ : from (bits x1 x0 x1) ≡ 5
_ = refl

_ : to 5 ≡ bits x1 x0 x1
_ = refl
