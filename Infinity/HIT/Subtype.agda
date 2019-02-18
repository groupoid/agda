{-# OPTIONS --cubical --safe #-}

module Infinity.HIT.Subtype where

open import Infinity.Proto 
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Inductive.Empty
open import Infinity.HIT.NType

R : ∀ (A : Set ℓ₁) ℓ₂ → Set (ℓ₁ ⊔ (ℓ-succ ℓ₂))
R A ℓ₂ = A → A → Set ℓ₂

R∅ : ∀ {A : Set ℓ} → R A ℓ-zero
R∅ _ _ = ⊥

SubtypeProp : ∀ ℓ₂ → (A : Set ℓ₁) → Set (ℓ₁ ⊔ (ℓ-succ ℓ₂)) 
SubtypeProp ℓ₂ A = Σ[ P ∈ (A → Set ℓ₂) ] ∀ x → isProp (P x)

module SubtypeProp {A : Set ℓ₁} (P : SubtypeProp ℓ₂ A) where 
  carr = π⃐ P
  prop = π⃑ P 
  
Subtype : ∀ {A : Set ℓ₁} (P : SubtypeProp ℓ₂ A) → Set (ℓ₁ ⊔ ℓ₂)
Subtype {A = A} P = Σ A (π⃐ P)

