{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Cohomology where 

open import Infinity.Proto
open import Infinity.Algebra.Base 
open import Infinity.Algebra.Abelian
open import Infinity.Algebra.Chain

-- Hⁿ : ℤ → Set ℓ → Set ℓ → Set (ℓ-succ ℓ)
-- Hⁿ' n X C = ∥ X → (B n C) ∥₀
