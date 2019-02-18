{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Abelian where

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Algebra.Group

is-abelian : Group ℓ → Set ℓ
is-abelian G = (a b : Group.E G) → (Group._∘_ G a b) ≡ (Group._∘_ G b a)

Abelian : ∀ ℓ → Set (ℓ-succ ℓ)
Abelian = λ ℓ → Σ (Group ℓ) is-abelian

Abᴳ₀ : Set₁
Abᴳ₀ = Abelian ℓ-zero

module Abelian (G : Abelian ℓ) where 
  grp  = π⃐ G  
  comm = π⃑ G
  open Group grp public 
