{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Cokernel where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Algebra.Base


module _ {G : Group ℓ₁} {H : Group ℓ₂} (ϕ : G →ᴳ H) (H-ab : is-abelian H) where 
  private 
    module G = Group G 
    module H = Abelian (H , H-ab)
    module ϕ = Homᴳ ϕ
    
  -- coker-R : R H.E (ℓ₁ ⊔ ℓ₂)
  -- coker-R h₁ h₂ = ? -- ∥ hfiber ϕ.f (h₁ H.- h₂) ∥₋₁
  
  -- private 
  --   coker-E : Set (ℓ₁ ⊔ ℓ₂)
  --   coker-E = Quot₀ coker-R 
