{-# OPTIONS --cubical --safe #-}
module Infinity.Path where

open import Agda.Builtin.Sigma public renaming (fst to π⃐; snd to π⃑)
open import Infinity.Core public

module _ {ℓ} {A : Set ℓ} where

  refl : {x : A} → x ≡ x
  refl {x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  cong : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A} (f : (a : A) → B a) (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
  cong f p = λ i → f (p i)

  coe : ∀ {ℓ : Level} {A B : Set ℓ} → A ≡ B → A → B
  coe p a = primComp (λ i → p i) i0 (λ _ → empty) a

  compPath : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  compPath {x = x} p q i = hcomp (λ j → \ { (i = i0) → x ; (i = i1) → q j }) (p i)

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

module _ {ℓ} {A : Set ℓ} where

  singl : (a : A) → Set ℓ
  singl a = Σ A (λ x → a ≡ x)

  contrSingl : {a b : A} (p : a ≡ b) → Path (singl a) (a , refl) (b , p)
  contrSingl p i = (p i , λ j → p (i ∧ j))

module _ {ℓ} {A : I → Set ℓ} {x : A i0} {y : A i1} where

  toPathP : transp A i0 x ≡ y → PathP A x y
  toPathP p i = hcomp (λ j → λ { (i = i0) → x ; (i = i1) → p j }) (transp (λ j → A (i ∧ j)) (~ i) x)

  fromPathP : PathP A x y → transp A i0 x ≡ y
  fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)

module _ {ℓ} where

  isContr : Set ℓ → Set ℓ
  isContr A = Σ A (λ x → ∀ y → x ≡ y)

  isProp : Set ℓ → Set ℓ
  isProp A = (x y : A) → x ≡ y

  isSet : Set ℓ → Set ℓ
  isSet A = (x y : A) → isProp (x ≡ y)
