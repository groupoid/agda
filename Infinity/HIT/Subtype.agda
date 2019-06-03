{-# OPTIONS --cubical --safe #-}

module Infinity.HIT.Subtype where

open import Infinity.Proto 
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Retract
open import Infinity.Inductive.Empty
open import Infinity.HIT.NType

R : ∀ (A : Set ℓ₁) ℓ₂ → Set (ℓ₁ ⊔ (ℓ-succ ℓ₂))
R A ℓ₂ = A → A → Set ℓ₂

R∅ : ∀ {A : Set ℓ} → R A ℓ-zero
R∅ _ _ = ⊥

module _ {A : Set ℓ₁} {ℓ₂} (r : R A ℓ₂) where 
  is-refl : Set (ℓ₁ ⊔ ℓ₂)
  is-refl = ∀ a → r a a 
  
  is-sym : Set (ℓ₁ ⊔ ℓ₂)
  is-sym = ∀ {a b} → r a b → r b a 
  
  is-trans : Set (ℓ₁ ⊔ ℓ₂)
  is-trans = ∀ {a b c} → r a b → r b c → r a c 
  
SubtypeProp : ∀ ℓ₂ → (A : Set ℓ₁) → Set (ℓ₁ ⊔ (ℓ-succ ℓ₂)) 
SubtypeProp ℓ₂ A = Σ[ P ∈ (A → Set ℓ₂) ] ∀ x → isProp (P x)

module SubtypeProp {A : Set ℓ₁} (P : SubtypeProp ℓ₂ A) where 
  carr = π⃐ P
  prop = π⃑ P 
  
Subtype : ∀ {A : Set ℓ₁} (P : SubtypeProp ℓ₂ A) → Set (ℓ₁ ⊔ ℓ₂)
Subtype {A = A} P = Σ A (π⃐ P)

module _ {A : Set ℓ₁} (P : Σ[ C ∈ (A → Set ℓ₁) ] ∀ x → isProp (C x)) where -- (P : SubtypeProp ℓ₂ A) where 
  private 
    module P = SubtypeProp P 
    
  -- instance 
    -- Subtype-level
    
  -- TODO : equivalence typeclass 
  _<:≡:>_ : (a b : Subtype P) → Set ℓ₁
  a <:≡:> b = π⃐ a ≡ π⃐ b
  
  -- <:≡:>→≡ : ∀ {a b : Subtype P} → a <:≡:> b → a ≡ b 
  <:≡:>→≡ : ∀ {a b : Σ A (P.carr)} → a <:≡:> b → a ≡ b 
  -- <:≡:>→≡ {a = a} {b = b} s = Σ-entwine a b s (prop-≡ _) --(λ p → {!!}) -- {!!} -- (λ p x y → p x y)
  <:≡:>→≡ {a = a} {b = b} s = coe (sym (propΣ-≡ P.prop a b)) (a ≡ b)

record IsEquivClass (X : Set ℓ₁) (_~_ : R X ℓ₂) (P : SubtypeProp ℓ₂ X) : Set (ℓ₁ ⊔ ℓ₂) where 
  constructor isEquivClass
  private 
    module P = SubtypeProp P
  field 
    inhab : isContr (Subtype P) 
    lift  : ∀ (x₁ x₂ : X) → x₁ ~ x₂ → P.carr x₁ → P.carr x₂ 
    rel   : ∀ (x₁ x₂ : X) → P.carr x₁ → P.carr x₂ → x₁ ~ x₂
