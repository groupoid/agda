{-# OPTIONS --cubical --safe #-}

module Infinity.Sigma where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Inductive.Empty

Σ-map : ∀ {ℓ} {A : Set ℓ} {B C : A → Set ℓ} → ((a : A) → B a → C a) → Σ A B → Σ A C
Σ-map f (a , b) = (a , f a b)

Σ-ind : ∀ {ℓ₁ ℓ₂} {S : Set ℓ₁} {T : S → Set ℓ₁} {P : Σ S T → Set ℓ₂} → ((s : S)(t : T s) → P (s , t)) → (p : Σ S T) → P p
(Σ-ind p) (s , t) = p s t

nonDepPath : ∀ {ℓ} {A : Set ℓ} → (t u : A) → (t ≡ u) ≡ (PathP (λ i → A) t u)
nonDepPath _ _ = refl

-- lemTransp : ∀ {ℓ} {A : Set ℓ} (a : A) → Path a (transport (λ _ → A) a)
-- lemTransp {A} a i = safeFill (λ _ → A) i0 (λ _ → empty) (inc a) i

∃ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → (A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
∃ = Σ _

∄ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → (A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
∄ P = ¬ ∃ P

-- Σ! : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
-- Σ! = isContr ⦂ Σ

-- syntax Σ! A (λ x → B) = Σ[ x ∈ A ] B

infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infixl 40 _×_

_×_ : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
A × B = Σ[ _ ∈ A ] B

uncurry : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (x : A) → B x → Set ℓ₃} → (∀ x y → C x y) → (∀ s → C (π⃐ s) (π⃑ s))
uncurry f (x , y) = f x y

