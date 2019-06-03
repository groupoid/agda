{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Quotient where 

open import Infinity.Proto
open import Infinity.Path

data _/_ (A : Set ℓ₁) (R : A → A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  [_] : (a : A) → A / R 
  eq  : (a b : A) → (r : R a b) → [ a ] ≡ [ b ]
  sq  : (a b : A / R) → (p q : a ≡ b) → p ≡ q
