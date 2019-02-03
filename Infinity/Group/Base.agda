{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Infinity.Group.Base where

open import Infinity.Proto hiding (_∘_)
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Inductive.Z

record Group-Skeleton (E : Set ℓ) : Set ℓ where 
  constructor group
  field 
    id  :         E 
    _⁻¹ : E     → E
    _∘_ : E → E → E 
    {{⊤⃐}} : ∀ A     → id ∘ A      ≡ A 
    {{assoc}}     : ∀ A B C → (A ∘ B) ∘ C ≡ A ∘ (B ∘ C)
    {{_⁻¹⃐}}  : ∀ A     → (A  ⁻¹) ∘ A ≡ id

  private 
    infix 80 _∘_

  abstract
    _⁻¹⃑ : ∀ G → G ∘ G ⁻¹ ≡ id 
    _⁻¹⃑ = {!!}
    
    _⁻¹⁻¹ : (g : E) → (g ⁻¹) ⁻¹ ≡ g 
    g ⁻¹⁻¹ = {!!}

  -- exp : E → ℤ → E 
  -- exp e (pos 0) = id 
  -- exp e (pos 1) = e
  -- exp e (pos 2) = e ∘ (exp e (pos 1))
  -- exp e (negsucc 0) = e ⁻¹
  -- exp e (negsucc (S n)) = e ⁻¹ ∘ (exp e (negsucc n))
  
  _-_ : E → E → E 
  g - h = g ∘ h ⁻¹
  
  conj : E → E → E 
  conj g h = (g ∘ h) ∘ g ⁻¹
  
record Group ℓ : Set (ℓ-succ ℓ) where 
  constructor group 
  field 
    E : Set ℓ 
    -- {{.E-level}} : has-level 0 E 
    skeleton : Group-Skeleton E 
  open Group-Skeleton skeleton public 
      
Group₀ : Set₁ 
Group₀ = Group ℓ-zero

is-trivial : Group ℓ → Set ℓ 
is-trivial G = ∀ g → g ≡ Group.id G

