{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Theory.Taylor where

open import Infinity.Proto
open import Infinity.Sigma

-- Δ : ∀ {o ℓ e} → (C : Category o ℓ e) → Functor C (Product C C)
-- Δ C = record
--   { F₀ = λ x → x , x
--   ; F₁ = λ f → f , f
--   ; identity = refl , refl
--   ; homomorphism = refl , refl
--   ; F-resp-≡ = λ x → x , x
--   }
--   where 
--   open Category C
--   open Equiv

Δ : Set ℓ → Set ℓ
Δ C = C × C 

-- comonad-split : ∀ {n : ℕ} n-Comonad n ≡ Δ* ∘ cr n

-- P : (n : ℕ) → Mc (N (∀ {m : ℕ} → n-Comonad (succ m) (succ n) → id))
