{-# OPTIONS --cubical --safe #-}

module Infinity.Top.Cover where 

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Path
open import Infinity.Top.Space 
open import Infinity.Top.Predicate 
open import Infinity.Category.Cat
open import Infinity.Category.Topos 

-- record Cover {S : Space} (I : Set ℓ) : Set ℓ where 
--     field 
--         at       : (i : I) → Pred (Space.C S)
--         at-open  : (i : I) → Space.Open (at i)
--         at-subs  : (i : I) → at i ⊆ Pred (Space.C S)
--         covering : (e : Space.C S) → Pred (Space.C S) e → Σ[ i ∈ I ] at i e
