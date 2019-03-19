{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.HSpace where 

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Pointed

record HSpace-Skeleton (A : Set₊ ℓ) : Set ℓ where 
  constructor ℍˢᵖ-Skeleton 
  field 
    μ₊ : A ×₊ A →₊ A
    
    {{unit-l₊}} : μ₊ ∘₊ ×-π⃑₊ A A ∼₊ id₊ A 
    {{unit-r₊}} : μ₊ ∘₊ ×-π⃐₊ A A ∼₊ id₊ A 
    
  μ : ∣ A ∣ → ∣ A ∣ → ∣ A ∣ 
  μ = curry (π⃐ μ₊)

  -- unit-l : ∀ a → μ (pt A) a ≡ a 
  -- unit-l = π⃐ unit-l₊
  
  -- ∪nit-r : ∀ a → μ a (pt A) ≡ A 
  -- unit-r = π⃐ unit_r₊
