{-# OPTIONS --cubical --safe #-}

module Infinity.Proto where

open import Agda.Builtin.Nat public using (zero; _+_; _*_) renaming (Nat to ℕ ; suc to succ)
open import Infinity.Core public

module _ {A : Set ℓ₁} where

  flip : ∀ {B : Set ℓ₂} {C : A → B → Set ℓ₃} → ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
  flip f = λ y x → f x y

  infixr 80 _∘_

  _∘_ : ∀ {B :      A        → Set ℓ₂} 
          {C : (a : A) → B a → Set ℓ₃}
          (g : {a : A} → (b : B a) → C a b) 
          (f : (a : A) →      B a) 
        → (a : A) → C a (f a)
  g ∘ f = λ a → g (f a)

  _⦂_ : ∀ {B :      A                      → Set ℓ₂} 
          {C : (a : A) →      B a          → Set ℓ₃} 
          {D : (a : A) → (b : B a) → C a b → Set ℓ₄}
          (g : {a : A} {b : B a} → (c : C a b) → D a b c) 
          (f : (a : A) (b : B a) →      C a b)
        → (a : A) (b : B a) → D a b (f a b)
  g ⦂ f = λ a b → g (f a b)
  
  _⦂⦂_ : ∀ {B :      A                                                        → Set ℓ₂} 
           {C : (a : A) →      B a                                            → Set ℓ₃} 
           {D : (a : A) → (b : B a) →      C a b                              → Set ℓ₄}
           {E : (a : A) → (b : B a) → (c : C a b) →      D a b c              → Set ℓ₅}
           {F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → E a b c d → Set ℓ₆}
           (g : {a : A} {b : B a} {c : C a b} {d : D a b c} (e : E a b c d) → F a b c d e) 
           (f : (a : A) (b : B a) (c : C a b) (d : D a b c) →    E a b c d)
         → (a : A) (b : B a) (c : C a b) (d : D a b c) → F a b c d (f a b c d)
  g ⦂⦂ f = λ a b c d → g (f a b c d)

idFun : (A : Set ℓ) → A → A
idFun A x = x

-- const : ∀ {A : Set ℓ} {B : A → Set ℓ} → (a : A) → B a → A 
const : ∀ {A B : Set ℓ} → A → B → A 
const = λ a _ → a 

apply : ∀ {A B : Set ℓ} (f : A → B) (x : A) → B
apply f x = f x

infixr 0 _$_ 
_$_ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → (∀ x → B x) → (∀ x → B x)
f $ x = f x 

typeof : ∀ {A : Set ℓ} → A → Set ℓ
typeof {A = A} _ = A

instanceof : ∀ {A : Set ℓ} {{a : A}} → A
instanceof {{a}} = a

record ⇑ (X : Set ℓ₁) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor ↑
    field ↓ : X

open ⇑ public
