{-# OPTIONS --cubical --safe #-}

module Infinity.Path where

open import Infinity.Core public
open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Inductive.Empty

compPath : ∀ {A : Set ℓ} {x y z : A} → Path A x y → Path A y z → Path A x z
compPath {_} {A} {x} {y} p q = λ i → primComp (λ j → A) _ (λ j → λ { (i = i1) → q j ; (i = i0) → x }) (p i)

trans : ∀ {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {x = x} p q i = hcomp (λ j → \ { (i = i0) → x ; (i = i1) → q j }) (p i)

refl : ∀ {A : Set ℓ} {x : A} → x ≡ x
refl {x = x} = λ _ → x

sym : ∀ {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym p = λ i → p (~ i)

cong : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} {x y : A} (f : (a : A) → B a) (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
cong f p = λ i → f (p i)

cong₂ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (a : A) → B a → Set ℓ₃} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} 
      → (f : (a : A) → (b : B a) → C a b) (p : a₁ ≡ a₂) (q : PathP (λ j → B (p j)) b₁ b₂) 
      → PathP (λ i → C (p i) (q i)) (f a₁ b₁) (f a₂ b₂)
cong₂ f p q = λ i → f (p i) (q i)

infixl 4 cong 
syntax cong c p = p |in c 

coe : ∀ {A : Set ℓ₁} {B : Set ℓ₁} → A ≡ B → A → B
coe p a = primComp (λ i → p i) i0 (λ _ → empty) a

module _ {A : Set ℓ₁} {x : A} (P : ∀ y → x ≡ y → Set ℓ₂) (d : P x refl) where

  J : ∀ {y : A} → (p : x ≡ y) → P y p
  J p = transp (λ i → P (p i) (λ j → p (i ∧ j))) i0 d

  JRefl : J refl ≡ d
  JRefl i = transp (λ _ → P x refl) i d

module _ {A : Set ℓ₁} (B : A → Set ℓ₂) where

  subst : ∀ {a b : A} (p : a ≡ b) → B a → B b
  subst p pa = transp (λ i → B (p i)) i0 pa

  substRefl : ∀ {a : A} (pa : B a) → subst refl pa ≡ pa
  substRefl {a = a} pa i = transp (λ _ → B a) i pa

  funExt : ∀ {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
  -- funExt = flip
  funExt p i x = p x i

transpRefl : (A : Set ℓ) (u₀ : A) → PathP (λ _ → A) (transp (λ _ → A) i0 u₀) u₀
transpRefl A u₀ i = transp (λ _ → A) i u₀

comp↑ : ∀ {A : Set ℓ} {a₁ a₂ b₁ b₂ : A} (p : a₁ ≡ a₂) (q : b₁ ≡ b₂) (r : a₁ ≡ b₁) → a₂ ≡ b₂ 
comp↑ {A = A} p q r = λ i → primComp (λ _ → A) _ (λ j → λ { (i = i0) → p j ; (i = i1) → q j }) (r i)

comp↓ : ∀ {A : Set ℓ} {a₁ a₂ b₁ b₂ : A} (p : a₁ ≡ a₂) (q : b₁ ≡ b₂) (r : a₂ ≡ b₂) → a₁ ≡ b₁
comp↓ p q = comp↑ (sym p) (sym q) 
