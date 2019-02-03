{-# OPTIONS --cubical --safe #-}

module Infinity.Group.Homomorphism where 

open import Infinity.Proto
open import Infinity.Group.Base 

record Homᴳ (G : Group ℓ₁) (H : Group ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where 
  constructor homᴳ
  private 
    module G = Group G 
    module H = Group H 
    _∘ᴳ_ = G._∘_
    _∘ᴴ_ = H._∘_
  field 
    f : G.E → H.E 
    {{.preserves-composition}} : ∀ g₁ g₂ → f (g₁ ∘ᴳ g₂) ≡ (f g₁) ∘ᴴ (f g₂) 
  -- open Homᴳ-Skeleton {GS = G.Skeleton} {HS = H.Skeleton} 
  --   record {f = f ; preserves-composition = preserves-composition } hiding (f ; preserves-composition) public

infix 0 _→ᴳ_ 
_→ᴳ_ = Homᴳ 
