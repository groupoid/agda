{-# OPTIONS --cubical --safe #-}

module Infinity.Group.Abelian where

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Group.Base

is-abelian : Group ℓ → Set ℓ
is-abelian G = (a b : Group.E G) → (Group._∘_ G a b) ≡ (Group._∘_ G b a)

Abᴳ : ∀ ℓ → Set (ℓ-succ ℓ)
Abᴳ = λ ℓ → Σ (Group ℓ) is-abelian

Abᴳ₀ : Set₁
Abᴳ₀ = Abᴳ ℓ-zero

module Abᴳ (G : Abᴳ ℓ) where 
  grp  = π⃐ G  
  comm = π⃑ G
  open Group grp public 
