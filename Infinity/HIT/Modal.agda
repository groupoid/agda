{-# OPTIONS --cubical --safe #-}

module Infinity.HIT.Modal where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.HIT.NType

record Modality ℓ : Set (ℓ-succ ℓ) where 
  field 
    isModal : Set ℓ → Set ℓ
    isModalIsProp : ∀ {A : Set ℓ} → isProp (isModal A)
    
    ◯ : Set ℓ → Set ℓ 
    ◯-isModal : ∀ {A : Set ℓ} → isModal (◯ A)
    
    η : ∀ {A : Set ℓ} → A → ◯ A

    ◯-elim : ∀ {A : Set ℓ} {B : ◯ A → Set ℓ} (B-modal : (a : ◯ A) → isModal (B a)) (f : (x : A) → (B (η x))) → (x : ◯ A) → B x
  
    ◯-elimβ : ∀ {A : Set ℓ} {B : ◯ A → Set ℓ} (B-modal : (x : ◯ A) → isModal (B x)) (f : (x : A) → (B (η x))) → (a : A) → ◯-elim B-modal f (η a) ≡ f a

    ◯≡isModal : ∀ {A : Set ℓ} (x y : ◯ A) → isModal (x ≡ y)

  ◯-Type : Set (ℓ-succ ℓ)
  ◯-Type = Σ (Set ℓ) isModal 
  
  module ◯-Elim {A : Set ℓ} {B : ◯ A → Set ℓ} (B-modal : (a : ◯ A) → isModal (B a)) (η* : (a : A) → (B (η a))) where
    f : (a : ◯ A) → B a 
    f = ◯-elim B-modal η* 
    
    η-β-id : (a : A) → ◯-elim B-modal η* (η a) ≡ η* a 
    η-β-id = ◯-elimβ B-modal η*

  module ◯-Rec {A B : Set ℓ} (B-modal : isModal B) (η* : A → B) = ◯-Elim (λ _ → B-modal) η*
  
  
