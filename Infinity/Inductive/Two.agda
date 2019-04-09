{-# OPTIONS --cubical --safe #-}

module Infinity.Inductive.Two where

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Path 

-- Boolean

data 𝟚 : Set where
    𝟘 : 𝟚
    𝟙 : 𝟚

𝟚-ind : ∀ {P : 𝟚 → Set ℓ} → P 𝟙 → P 𝟘 → (b : 𝟚) → P b
𝟚-ind t _ 𝟙 = t
𝟚-ind _ f 𝟘 = f

_⊎Σ_ : Set ℓ → Set ℓ → Set ℓ
S ⊎Σ T = Σ 𝟚 (𝟚-ind S T)

-- 𝟘≠𝟙 : 𝟘 ≡ 𝟙
-- 𝟘≠𝟙 ()

_≤_ : (a b : 𝟚) → Set
a ≤ b = a ≡ 𝟙 → b ≡ 𝟙

_≥_ : (a b : 𝟚) → Set
_≥_ = flip _≤_

shannon : ∀ {A : Set} (f : 𝟚 → A) → 𝟚 → A 
shannon = apply

shannon-≡ : ∀ {A : Set} (f : 𝟚 → A) → f ≡ shannon f
shannon-≡ f = refl
