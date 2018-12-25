{-# OPTIONS --cubical #-}

module Infinity.Cohesion.Im where 

open import Infinity.Proto
open import Infinity.Sigma

postulate 
    ℑ : ∀ {i} → Set i → Set i
    ι : ∀ {ℓ} {A : Set ℓ} → A → ℑ A 
    
ℑ-unit-at : ∀ {ℓ} → (A : Set ℓ) → (A → ℑ A)
ℑ-unit-at A = ι {_} {A}

postulate 
  _is-coreduced : ∀ {ℓ} → Set ℓ → Set ℓ
-- A is-coreduced = ι {_} {A} isEquiv

ℑ-Set₀ : Set₁
ℑ-Set₀ = Σ[ A ∈ Set₀ ] A is-coreduced

ι-ℑ-Set₀ : ℑ-Set₀ → Set₀
ι-ℑ-Set₀ (A , _) = A

postulate 
    ℑ-is-coreduced : ∀ {ℓ} → (A : Set ℓ) → (ℑ A) is-coreduced 
    
