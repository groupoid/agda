{-# OPTIONS --cubical --safe #-}

module Infinity.Iso where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Univ
open import Infinity.Retract
open import Infinity.HIT.NType

module _ {A : Set ℓ₁} {B : A → Set ℓ₂} where 
    -- TODO : Beautiful case for beautiful combinators 
    Σ-≡ : (t u : Σ A B) → (t ≡ u) ≡ (Σ[ p ∈ (π⃐ t ≡ π⃐ u) ] PathP (λ i → B (p i)) (π⃑ t) (π⃑ u))
    Σ-≡ t u = ≃→≡ f g (λ p → refl {x = p}) (λ q → refl {x = q})
      where T₁ : Set (ℓ₁ ⊔ ℓ₂)
            T₁ = t ≡ u 
            T₂ : Set (ℓ₁ ⊔ ℓ₂)
            T₂ = Σ[ p ∈ (π⃐ t ≡ π⃐ u) ] PathP (λ i → B (p i)) (π⃑ t) (π⃑ u)
            f : (q : T₁) → T₂ 
            f q .π⃐ i = π⃐ (q i) 
            f q .π⃑ i = π⃑ (q i)
            g : (p : T₂) → T₁
            g p i .π⃐ = (π⃐ p) i 
            g p i .π⃑ = (π⃑ p) i
            
    Σ-entwine : (t u : Σ A B) (p : π⃐ t ≡ π⃐ u) (q : PathP (λ i → B (p i)) (π⃑ t) (π⃑ u)) → t ≡ u
    Σ-entwine t u p q = coe (sym (Σ-≡ t u)) (p , q)
    
-- module _ {A : Set ℓ₁} {B : A → Set ℓ₂} (pb : (x : A) → isProp (B x)) where
--     -- π⃑-isContr : (t u : Σ A B) (p : π⃐ t ≡ π⃐ u) → isContr (π⃑ t ≡ π⃑ u) 
--     -- π⃑-isContr t u p = inhProp→isContr ϕ (subst⁻¹ isProp ψ ω)

--     propΣ-≡ : (t u : Σ A B) → (t ≡ u) ≡ (π⃐ t ≡ π⃐ u)
--     propΣ-≡ trans p₂ p₁
--       where p₀ = Σ-≡ t u 
           
