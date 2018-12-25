{-# OPTIONS --cubical --safe #-}
module Infinity.Proto where

open import Agda.Builtin.Sigma public 
  renaming (fst to π⃐; snd to π⃑) 

open import Agda.Builtin.Nat public 
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)
  
open import Infinity.Core public

-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work with
-- (non-dependent) paths.
module _ {ℓ} {A : Set ℓ} where
  refl : {x : A} → x ≡ x
  refl {x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  cong : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A}
         (f : (a : A) → B a) (p : x ≡ y)
       → PathP (λ i → B (p i)) (f x) (f y)
  cong f p = λ i → f (p i)

  -- This is called compPath and not trans in order to eliminate
  -- confusion with transp
  compPath : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  compPath {x = x} p q i =
    hcomp (λ j → \ { (i = i0) → x
                   ; (i = i1) → q j }) (p i)

  infix  3 _≡-qed _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  1 ≡-proof_ begin_

  ≡-proof_ begin_ : {x y : A} → x ≡ y → x ≡ y
  ≡-proof x≡y = x≡y
  begin_ = ≡-proof_

  _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = compPath x≡y y≡z

  _≡-qed _∎ : (x : A) → x ≡ x
  _ ≡-qed  = refl
  _∎ = _≡-qed


-- Subst and functional extensionality

module _ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') where
  subst : {a b : A} (p : a ≡ b) → B a → B b
  subst p pa = transp (λ i → B (p i)) i0 pa

  substRefl : {a : A} (pa : B a) → subst refl pa ≡ pa
  substRefl {a} pa i = transp (λ _ → B a) i pa

  funExt : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
  funExt p i x = p x i


-- Transporting in a constant family is the identity function (up to a
-- path). If we would have regularity this would be definitional.
transpRefl : ∀ {ℓ} (A : Set ℓ) (u0 : A) →
             PathP (λ _ → A) (transp (λ _ → A) i0 u0) u0
transpRefl A u0 i = transp (λ _ → A) i u0


-- J for paths and its computation rule

module _ {ℓ ℓ'} {A : Set ℓ} {x : A}
         (P : ∀ y → x ≡ y → Set ℓ') (d : P x refl) where
  J : {y : A} → (p : x ≡ y) → P y p
  J p = transp (λ i → P (p i) (λ j → p (i ∧ j))) i0 d

  JRefl : J refl ≡ d
  JRefl i = transp (λ _ → P x refl) i d


-- Contractibility of singletons

module _ {ℓ} {A : Set ℓ} where
  singl : (a : A) → Set ℓ
  singl a = Σ A (λ x → a ≡ x)

  contrSingl : {a b : A} (p : a ≡ b) → Path (singl a) (a , refl) (b , p)
  contrSingl p i = (p i , λ j → p (i ∧ j))


-- Converting to and from a PathP

module _ {ℓ} {A : I → Set ℓ} {x : A i0} {y : A i1} where
  toPathP : transp A i0 x ≡ y → PathP A x y
  toPathP p i = hcomp (λ j → λ { (i = i0) → x
                               ; (i = i1) → p j })
                      (transp (λ j → A (i ∧ j)) (~ i) x)

  fromPathP : PathP A x y → transp A i0 x ≡ y
  fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)


-- Direct definitions of lower h-levels

module _ {ℓ} where
  isContr : Set ℓ → Set ℓ
  isContr A = Σ A (λ x → ∀ y → x ≡ y)

  isProp : Set ℓ → Set ℓ
  isProp A = (x y : A) → x ≡ y

  isSet : Set ℓ → Set ℓ
  isSet A = (x y : A) → isProp (x ≡ y)
  

-- Combinators

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} where 
  flip : ∀ {B : Set ℓ₂} {C : A → B → Set ℓ₃} → ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
  flip f = λ y x → f x y
  
  infixr 80 _∘_
  _∘_ : ∀ {B : A → Set ℓ₂} {C : (a : A) → (B a → Set ℓ₃)}
      (g : {a : A} → (x : B a) → (C a x)) → (f : (x : A) → B x) → (x : A) → C x (f x)
  g ∘ f = λ x → g (f x)

  _⦂_ : ∀ {B : A → Set ℓ₂} {C : (a : A) → (B a → Set ℓ₃)} {D : (a : A) → (b : B a) → C a b → Set ℓ₃}
      → (g : {a : A} {b : B a} → (x : C a b) → D a b x) → (f : (x : A) → (y : B x) → C x y) → (x : A) → (y : B x) → D x y (f x y)
  g ⦂ f = λ x y → g (f x y)

apply : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (x : A) → B
apply f x = f x 

typeof : ∀ {ℓ} {A : Set ℓ} → A → Set ℓ
typeof {A = A} _ = A 

record ⇑ {ℓ₁ ℓ₂} (X : Set ℓ₁) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor ↑
    field ↓ : X 
open ⇑ public

coe : ∀ {ℓ : Level} {A B : Set ℓ} → A ≡ B → A → B
coe p a = primComp (λ i → p i) i0 (λ _ → empty) a 
