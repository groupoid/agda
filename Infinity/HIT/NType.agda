{-# OPTIONS --cubical --safe #-}

module Infinity.HIT.NType where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Inductive.Empty

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
  
nonDepPath : ∀ {ℓ} {A : Set ℓ} → (t u : A) → (t ≡ u) ≡ (PathP (λ i → A) t u)
nonDepPath _ _ = refl

isOfHLevel : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ
isOfHLevel zero A = isContr A
isOfHLevel (succ n) A = (x y : A) → isOfHLevel n (x ≡ y)

HLevel : ∀ {ℓ} → ℕ → Set _
HLevel {ℓ} n = Σ[ A ∈ Set ℓ ] (isOfHLevel n A)

isContr→isProp : ∀ {A : Set ℓ} → isContr A → isProp A
isContr→isProp (x , p) a b i = hcomp (λ j → λ { (i = i0) → p a j ; (i = i1) → p b j }) x

inhProp→isContr : ∀ {A : Set ℓ} → A → isProp A → isContr A
inhProp→isContr x h = x , h x

isProp⊥ : isProp ⊥
isProp⊥ x = ⊥-elim x

isProp¬ : ∀ {l} → (A : Set l) → isProp (¬ A)
isProp¬ A p q i x = isProp⊥ (p x) (q x) i

isProp→isSet : ∀ {A : Set ℓ} → isProp A → isSet A
isProp→isSet h a b p q j i = hcomp (λ k → λ { (i = i0) → h a a k ; (i = i1) → h a b k
                                            ; (j = i0) → h a (p i) k ; (j = i1) → h a (q i) k }) a

isPropIsOfHLevel1 : ∀ {A : Set ℓ} → isProp A → isOfHLevel 1 A
isPropIsOfHLevel1 h x y = inhProp→isContr (h x y) (isProp→isSet h x y)

isPropIsProp : ∀ {A : Set ℓ} → isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

isPropIsSet : ∀ {A : Set ℓ} → isProp (isSet A)
isPropIsSet f g i a b = isPropIsProp (f a b) (g a b) i

isPropIsContr : ∀ {A : Set ℓ} → isProp (isContr A)
isPropIsContr z0 z1 j = ( z0 .π⃑ (z1 .π⃐) j , λ x i → hcomp (λ k → λ { (i = i0) → z0 .π⃑ (z1 .π⃐) j
                                                                   ; (i = i1) → z0 .π⃑ x (j ∨ k)
                                                                   ; (j = i0) → z0 .π⃑ x (i ∧ k)
                                                                   ; (j = i1) → z1 .π⃑ x i }) (z0 .π⃑ (z1 .π⃑ x i) j))
                                                                   
