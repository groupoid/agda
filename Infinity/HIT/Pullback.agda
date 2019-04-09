{-# OPTIONS --cubical #-}

module Infinity.HIT.Pullback where

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Inductive.One

pullback : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (f : A → C) (g : B → C) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
pullback {A = A} {B = B} f g = Σ[ a ∈ A ] Σ[ b ∈ B ] f a ≡ g b

kernel : ∀ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) → Set (ℓ₁ ⊔ ℓ₂)
kernel {A = A} {B = B} f = pullback {A = A} {A} {B} f f 

hofiber : ∀ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (b : B) → Set (ℓ₁ ⊔ ℓ₂)
hofiber {ℓ₁} {ℓ₂} {A = A} {B = B} f b = pullback {ℓ₁} {ℓ₂} {A = A} {⊤} {B} f λ (_ : ⊤) → b

pb₁ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {f : A → C} {g : B → C} (p : pullback f g) → A
pb₁ = π⃐ 

pb₂ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {f : A → C} {g : B → C} (p : pullback f g) → B
pb₂ = π⃐ ∘ π⃑

pb₃ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {f : A → C} {g : B → C} (pb : pullback f g) → f (pb₁ pb) ≡ g (pb₂ pb)
pb₃ = π⃑ ∘ π⃑

induced : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {E : Set ℓ₄} {f : A → C} {g : B → C} (e₁ : E → A) (e₂ : E → B) 
        → (h : (e : E) → (f ∘ e₁) e ≡ (g ∘ e₂) e) → (e : E) → pullback f g 
induced e₁ e₂ h e = (e₁ e , e₂ e , h e)
