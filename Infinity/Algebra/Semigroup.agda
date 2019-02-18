{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Semigroup where 

open import Infinity.Proto hiding (_∘_)
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Inductive.Z

record Semigroup-Skeleton (E : Set ℓ) : Set ℓ where 
  constructor semigroup
  field 
    id        :         E 
    _∘_       : E → E → E 
    {{⊤⃐}}     : ∀ A     → id ∘ A      ≡ A 
    {{assoc}} : ∀ A B C → (A ∘ B) ∘ C ≡ A ∘ (B ∘ C)

  private 
    infix 80 _∘_

record Semigroup ℓ : Set (ℓ-succ ℓ) where 
  constructor semigroup 
  field 
    E : Set ℓ 
    -- {{.E-level}} : has-level 0 E 
    skeleton : Semigroup-Skeleton E 
  open Semigroup-Skeleton skeleton public 
      
Semigroup₀ : Set₁ 
Semigroup₀ = Semigroup ℓ-zero

is-trivial : Semigroup ℓ → Set ℓ 
is-trivial G = ∀ g → g ≡ Semigroup.id G
