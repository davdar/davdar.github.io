{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Lc16 where

import Data.Map (Map)
import qualified Data.Map as Map

-- x ∈ vname ≈ symbol
-- cn ∈ cname ≈ symbol
-- fn ∈ fname ≈ symbol
-- mn ∈ mname ≈ symbol

-- e ∈ expr ⩴ i | e + e | e × e 
--          | x | LET x = e IN e
--          | NEW cn(e,…,e)
--          | e.fn
--          | e.fn ← e
--          | e.mn(e)    -- all methods take exactly one argument

-- _;_ ∈ expr × expr → expr

-- cd ∈ cdecl ⩴ CLASS cn FIELDS fn … fn ~ md … md

-- md ∈ mdecl ⩴ METHOD mn(x) ⇒ e

-- p ∈ prog ⩴ cd … cd DO e

-- o ∈ object ⩴ OBJECT cn({fn↦ℓ,…,fn↦ℓ}) {mn↦[FUN(x)⇒e],…,mn↦[FUN(x)⇒e]}
--
-- v ∈ value ⩴ i | o

-- ℓ ∈ loc ≈ ℕ

-- γ ∈ env ≜ vname ⇀ value
--
-- σ ∈ store ≜ loc ⇀ value

-- fresh-loc ∈ store → loc

-- alloc ∈ store × value → loc × store

-- alloc-many ∈ store × list(value) → list(loc) × store

-- lookup-classs ∈ list(cdecl) × cname ⇀ cdecl

-- build-field-map ∈ list(fname) × list(loc) ⇀ (fname ⇀ loc)

-- build-method-map ∈ list(mdecl) ⇀ (mname ⇀ (vname × expr)))

-- interp ∈ list(cdecl) × env × store × expr ⇀ value × store

-- interp-many ∈ list(cdecl) × env × store × list(expr) ⇀ list(value) × store
