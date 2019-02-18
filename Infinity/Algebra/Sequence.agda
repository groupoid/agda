{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Sequence where 

open import Infinity.Proto hiding (_∘_)
open import Infinity.Path
open import Infinity.Algebra.Base 

-- record Semigroup-Skeleton (E : Set ℓ) : Set ℓ where 
--   constructor semigroup
--   field 
--     id        :         E 
--     _∘_       : E → E → E 
--     {{⊤⃐}}     : ∀ A     → id ∘ A      ≡ A 
--     {{assoc}} : ∀ A B C → (A ∘ B) ∘ C ≡ A ∘ (B ∘ C)

--   private 
--     infix 80 _∘_

-- record Semigroup ℓ : Set (ℓ-succ ℓ) where 
--   constructor semigroup 
--   field 
--     E : Set ℓ 
--     -- {{.E-level}} : has-level 0 E 
--     skeleton : Semigroup-Skeleton E 
--   open Semigroup-Skeleton skeleton public 
      
-- Semigroup₀ : Set₁ 
-- Semigroup₀ = Semigroup ℓ-zero

-- is-trivial : Semigroup ℓ → Set ℓ 
-- is-trivial G = ∀ g → g ≡ Semigroup.id G

module _ {G : Group ℓ₁} {H : Group ℓ₂} {K : Group ℓ₃} (φ : G →ᴳ H) (ψ : H →ᴳ K) where 
  private 
    module G = Group G 
    module H = Group H
    module K = Group K
    module φ = Homᴳ  φ
    module ψ = Homᴳ  ψ
    
  -- TODO : group isomorphism
  -- record is-exact : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  --   field 
  --     im-sub-ker : im-prop ϕ ⊆ᴳ ker-prop ψ
  --     ker-sub-im : ker-prop ψ ⊆ᴳ im-prop ϕ
    
