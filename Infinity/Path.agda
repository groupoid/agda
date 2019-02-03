{-# OPTIONS --cubical --safe #-}

module Infinity.Path where

open import Infinity.Core public
open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Inductive.Empty

module _ {ℓ} {A : Set ℓ} where

  compPath : {x y z : A} → Path A x y → Path A y z → Path A x z
  compPath {x} {y} p q = λ i → primComp (λ j → A) _ (λ j → λ { (i = i1) → q j ; (i = i0) → x }) (p i)

  trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} p q i = hcomp (λ j → \ { (i = i0) → x ; (i = i1) → q j }) (p i)

  refl : {x : A} → x ≡ x
  refl {x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  cong : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A} (f : (a : A) → B a) (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
  cong f p = λ i → f (p i)

  coe : ∀ {ℓ : Level} {A B : Set ℓ} → A ≡ B → A → B
  coe p a = primComp (λ i → p i) i0 (λ _ → empty) a

module _ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → x ≡ y → Set ℓ') (d : P x refl) where

  J : {y : A} → (p : x ≡ y) → P y p
  J p = transp (λ i → P (p i) (λ j → p (i ∧ j))) i0 d

  JRefl : J refl ≡ d
  JRefl i = transp (λ _ → P x refl) i d

module _ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') where

  subst : {a b : A} (p : a ≡ b) → B a → B b
  subst p pa = transp (λ i → B (p i)) i0 pa

  substRefl : {a : A} (pa : B a) → subst refl pa ≡ pa
  substRefl {a} pa i = transp (λ _ → B a) i pa

  funExt : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
  funExt p i x = p x i

  transpRefl : ∀ {ℓ} (A : Set ℓ) (u0 : A) → PathP (λ _ → A) (transp (λ _ → A) i0 u0) u0
  transpRefl A u0 i = transp (λ _ → A) i u0
