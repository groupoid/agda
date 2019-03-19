{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Product.Tensor where 

open import Infinity.Proto 
open import Infinity.Sigma
open import Infinity.Algebra.Group.Base 
open import Infinity.Algebra.Group.Abelian

module _⊗_ (G : Abelian ℓ₁) (H : Abelian ℓ₂) where 
  
  private 
    module G = Abelian G 
    module H = Abelian H 
  
  pts : Set (ℓ₁ ⊔ ℓ₂)
  pts = G.E × H.E

  -- data R : Word pts → Word pts → Set (ℓ₁ ⊔ ℓ₂) where 
  --   π⃐ : (g₁ g₂ : G.E) (h     : H.E) → R (π⃐ (g₁ G.∘ g₂ , h) :: nil) (π⃐ (g₁ , h) :: π⃐ (g₂ , h) :: nil)
  --   π⃑ : (g     : G.E) (h₁ h₂ : H.E) → R (π⃐ (g , h₁ H.∘ h₂) :: nil) (π⃐ (g , h₁) :: π⃐ (g , h₂) :: nil)

  -- private 
  --   module ⊗-Free = FreeAbelian pts R

