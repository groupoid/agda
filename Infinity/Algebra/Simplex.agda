{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Simplex where 

open import Infinity.Proto 

module Simplex where 
  infix 0 _⊒_
  infix 1 _▸

  Δ₀ : Set
  Δ₀ = ℕ

  pattern ∅    = zero
  pattern _▸ Γ = succ Γ

  data _⊒_ : Δ₀ → Δ₀ → Set where 
    zero : ∅ ⊒ ∅ 
    face : ∀ {Γ Δ} (ρ : Δ ⊒ Γ  ) → Δ   ⊒ Γ ▸
    sgen : ∀ {Γ Δ} (ρ : Δ ⊒ Γ ▸) → Δ ▸ ⊒ Γ ▸

  pattern ε    = zero
  pattern δ_ ρ = face ρ
  pattern σ_ ρ = sgen ρ

  
