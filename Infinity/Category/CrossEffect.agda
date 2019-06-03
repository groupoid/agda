{-# OPTIONS --cubical --safe #-}

module Infinity.Category.CrossEffect where

open import Infinity.Proto
open import Infinity.Sigma

-- cr : (n : ℕ) (F : Set ℓ → Set ℓ) → C ^× n → Set ℓ
-- cr 0 F ()
-- cr 1 (F M) .⊕ (F unit) = F M 
-- cr 2 (F M₁ M₂) 
