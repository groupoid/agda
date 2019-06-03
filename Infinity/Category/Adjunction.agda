{-# OPTIONS --cubical --safe #-}

module Infinity.Category.Adjunction where

open import Infinity.Proto
open import Infinity.Category.Cat
open import Infinity.Category.Functor

record Adjunction {o ℓ e} {o₁ ℓ₁ e₁} {C : Category o ℓ e} {D : Category o₁ ℓ₁ e₁} 
  (F : Functor D C) (G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o₁ ⊔ ℓ₁ ⊔ e₁) where
    field
      unit   : NaturalTransformation idF (G ∘F F)
      counit : NaturalTransformation (F ∘F G) idF

      .zig : id ≡ (counit ∘ʳ F) ∘₁ (F ∘ˡ unit)
      .zag : id ≡ (G ∘ˡ counit) ∘₁ (unit ∘ʳ G)

    private module C = Category C renaming (_∘_ to _∘C_; _≡_ to _≡C_)
    private module D = Category D renaming (_∘_ to _∘D_; _≡_ to _≡D_)
    open C
    open D

    private module F = Functor F
    private module G = Functor G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)
    open F
    open G

    private module unit   = NaturalTransformation unit
    private module counit = NaturalTransformation counit
