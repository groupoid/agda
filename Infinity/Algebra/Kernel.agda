{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Infinity.Algebra.Kernel where 

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Univ
open import Infinity.HIT.Trunc
open import Infinity.HIT.Subtype
open import Infinity.Algebra.Base
open import Infinity.Algebra.Quotient
open import Infinity.Algebra.Subgroup

module _ {G : Group ℓ₁} {H : Group ℓ₂} (ϕ : G →ᴳ H) where
  private 
    module G = Group G 
    module H = Group H 
    module ϕ = Homᴳ ϕ 
    
  ker-propᴳ : SubgroupProp ℓ₂ G
  ker-propᴳ = record {K} where
    module K where 
      prop : G.E → Set ℓ₂ 
      prop g = {!!} -- ϕ.p g ≡ H.id 
      abstract 
        id : prop G.id
        id = ϕ.preserves-id
        
        _-_ : ∀ {e₁ e₂ : G.E} → prop e₁ → prop e₂ → prop (e₁ G.- e₂)
        -- _-_ {e₁} {e₂} p₁ p₂ = ϕ.preserves-_-_ e₁ e₂ ∘ ap₂ _-_ p₁ p₂ ∘ H.inv-r H.id
        _-_ = {!!}


module Kernel {G : Group ℓ₁} {H : Group ℓ₂} (ψ : G →ᴳ H) where 
  private 
    module G = Group G 
    module H = Group H
    module ψ = Homᴳ ψ
    
  module Ker = Subgroup (ker-propᴳ ψ)
    
  ker-R' : R H.E (ℓ₁ ⊔ ℓ₂)
  ker-R' h₁ h₂ = ∥ fiber ψ.p (h₁ H.- h₂) ∥

  -- ker-R : R Ker.E (ℓ₁ ⊔ ℓ₂)
  -- ker-R (h₁ , _) (h₂ , _) = ∥ fiber ψ.p (h₁ H.- h₂) ∥
  
  private
    -- ker-E : Set (ℓ₁ ⊔ ℓ₂)
    ker-E : Set (ℓ-succ ℓ₁ ⊔ ℓ-succ ℓ₂)
    ker-E = /₀ ker-R'
  
  -- kernel-skeleton : Group-Skeleton ker-E
  -- kernel-skeleton = record {K} where
  --   module K where 
  --     id : ker-E
  
  Ker : Group (ℓ₁ ⊔ ℓ₂)
  Ker = {!!} -- group _ kernel-skeleton
