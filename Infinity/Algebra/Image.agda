{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Infinity.Algebra.Image where 

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Univ
open import Infinity.HIT.Trunc
open import Infinity.HIT.NType
open import Infinity.HIT.Subtype
open import Infinity.Algebra.Base
open import Infinity.Algebra.Quotient
open import Infinity.Algebra.Subgroup

module _ {G : Group ℓ₁} {H : Group ℓ₂} (φ : G →ᴳ H) where 
  private 
    module G = Group G 
    module H = Group H 
    module φ = Homᴳ φ 

  im-propᴳ : SubgroupProp ℓ₂ H 
  im-propᴳ = record {M} where
    module M where
      prop : H.E → Set ℓ₂
      prop h = {!!} -- ∣ fiber φ.p h ∣₋₁

      -- level : (h : H.E) → isProp (prop h)
      -- level h = Trunc-level

      abstract
        id : prop H.id
        id = {!!} -- G.id , φ.preserves-id

        diff : {h₁ h₂ : H.E} → prop h₁ → prop h₂ → prop (h₁ H.- h₂)
        diff = {!!} -- trunc-map λ { (g₁ , p₁) (g₂ , p₂) → G._-_ g₁ g₂ , φ.preserves-difference g₁ g₂ ∘ ap₂ H._-_ p₁ p₂ }
        
module Image {G : Group ℓ₁} {H : Group ℓ₂} (φ : G →ᴳ H) where 
  private 
    module G = Group G 
    module H = Group H 
    module φ = Homᴳ φ 
    
    module Imφ = Subgroup (im-propᴳ φ)
      
  im-R : R Imφ.E (ℓ₁ ⊔ ℓ₂)
  im-R (h₁ , _) (h₂ , _) = {!!} -- ∥ fiber φ.p (h₁ H.- h₂) ∥₋₁
  
  private
    im-E : Set (ℓ-succ ℓ₁ ⊔ ℓ-succ ℓ₂)
    im-E = /₀ im-R
    
  image-skeleton : Group-Skeleton im-E
  image-skeleton = record {I} where
    module I where 
      id : im-E
      id = {!!}
  
  -- Image : Group (ℓ₁ ⊔ ℓ₂)
  Im : Group (ℓ-succ ℓ₁ ⊔ ℓ-succ ℓ₂)
  Im =  group _ image-skeleton
