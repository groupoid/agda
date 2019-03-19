{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Infinity.Algebra.Group.Quotient where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Equiv
open import Infinity.HIT.Subtype
open import Infinity.Algebra.Base 
open import Infinity.Algebra.Homomorphism

data Quotient {A : Set ℓ} (R : A → A → Set ℓ) : Set ℓ where 
  inj : A → Quotient {A = A} _
  eq  : (a b : A) {{_ : R a b}} → inj a ≡ inj b 
  
/₀ : ∀ {X : Set ℓ₁} (R : R X ℓ₂) → Set (ℓ₁ ⊔ (ℓ-succ ℓ₂))
/₀ {ℓ₂ = ℓ₂} {X = X} R = Σ[ A ∈ SubtypeProp ℓ₂ X ] IsEquivClass X R A

_/_ : (A : Set ℓ) (R : A → A → Set ℓ) → Set (ℓ-succ ℓ)
A / R = /₀ {X = A} R

infix 0 _/ᴳ_
_/ᴳ_ : (G : Group ℓ) (R : G →ᴳ G → Group ℓ) → Group (ℓ-succ ℓ)
G /ᴳ R = {!!} -- /₀ {X = G} R
