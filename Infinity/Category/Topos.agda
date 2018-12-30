{-# OPTIONS --cubical #-}

module Infinity.Category.Topos where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Category.Cat 
open import Infinity.Category.Functor

Presheaf : ∀ {Ob : Set ℓ} {Hom : Ob → Ob → Set ℓ} (C : Category Hom) → Set (ℓ-succ ℓ)
Presheaf C = Functor (C ᵒᵖ) SET λ _ → _
  
