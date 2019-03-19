{-# OPTIONS --cubical --safe #-}

module Infinity.Pointed where 

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Path

record Set₊ (ℓ : Level) : Set (ℓ-succ ℓ) where 
  constructor [_,_]₊ 
  field 
    ∣_∣ : Set ℓ
    pt  : ∣_∣
open Set₊ public

infixr 0 _→₊_ 
_→₊_ : Set₊ ℓ₁ → Set₊ ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
[ A , a ]₊ →₊ [ B , b ]₊ = Σ[ f ∈ (A → B) ] f a ≡ b 

id₊ : (A : Set₊ ℓ) → A →₊ A 
id₊ _ = (λ x → x) , refl

trans₊ : ∀ {A : Set₊ ℓ₁} {B : Set₊ ℓ₂} → A →₊ B 
trans₊ {B = B} = (λ x → pt B) , refl

Σ₊ : (A : Set₊ ℓ₁) → (∣ A ∣ → Set₊ ℓ₂) → Set₊ (ℓ₁ ⊔ ℓ₂)
Σ₊ [ A , a₀ ]₊ B = [ Σ A (∣_∣ ∘ B) , (a₀ , pt (B a₀)) ]₊

infix 2 Σ₊-syntax

Σ₊-syntax : (A : Set₊ ℓ₁) (B : ∣ A ∣ → Set₊ ℓ₂) → Set₊ (ℓ₁ ⊔ ℓ₂)
Σ₊-syntax = Σ₊

syntax Σ₊-syntax A (λ x → B) = Σ₊[ x ∈ A ] B

infix 40 _×₊_
_×₊_ : Set₊ ℓ₁ → Set₊ ℓ₂ → Set₊ (ℓ₁ ⊔ ℓ₂)
A ×₊ B = Σ₊ A (λ _ → B)

π⃐₊ : ∀ {A : Set₊ ℓ₁} {B : Set₊ ℓ₂} → A ×₊ B →₊ A 
π⃐₊ = π⃐ , refl

π⃑₊ : ∀ {A : Set₊ ℓ₁} {B : Set₊ ℓ₂} → A ×₊ B →₊ B 
π⃑₊ = π⃑ , refl

diag₊ : ∀ {A : Set₊ ℓ} → A →₊ A ×₊ A 
diag₊ = (λ x → x , x) , refl

×-π⃐₊ : (A : Set₊ ℓ₁) (B : Set₊ ℓ₂) → A →₊ A ×₊ B
×-π⃐₊ _ [ _ , b ]₊ = (λ a → a , b) , refl

×-π⃑₊ : (A : Set₊ ℓ₁) (B : Set₊ ℓ₂) → B →₊ A ×₊ B
×-π⃑₊ [ _ , a ]₊ _ = (λ b → a , b) , refl

-- infixr 3 _∼₊_ 
-- _∼₊_ : ∀ {A : Set₊ ℓ₁} {B : Set₊ ℓ₂} (f g : A →₊ B) → Set (ℓ₁ ⊔ ℓ₂) 
-- _∼₊_ {A = A} {B = B} (f , f₀) (g , g₀) = {!!} -- pointed congruence 

-- ∘₊-pt : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {a₁ a₂ : A} {b : B} (f : A → B) → a₁ ≡ a₂ → f a₂ ≡ b → f a₁ ≡ b
-- ∘₊-pt f p q = {!!} -- ap f p ∙ q

-- infixr 8 _∘₊_ 
-- _∘₊_ : ∀ {A : Set₊ ℓ₁} {B : Set₊ ℓ₂} {C : Set₊ ℓ₃} (g : B →₊ C) (f : A →₊ B) → A →₊ C 
-- (g , g₀) ∘₊ (f , f₀) = (g ∘ f) , ∘₊-pt g f₀ g₀
