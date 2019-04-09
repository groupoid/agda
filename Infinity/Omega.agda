{-# OPTIONS --cubical --safe #-}

module Infinity.Omega where 

open import Infinity.Proto hiding (_+_)
open import Infinity.Sigma
open import Infinity.Path
open import Infinity.Pointed
open import Infinity.Inductive.Z

Ω : Set₊ ℓ → Set₊ ℓ
Ω [ _ , x ]₊ = [ x ≡ x , refl ]₊

-- {-# TERMINATING #-}
-- Ωⁿ : ℤ → Set₊ ℓ → Set₊ ℓ
-- Ωⁿ (pos  zero   ) X = Ω X 
-- Ωⁿ (pos (succ n)) X = Ω (Ωⁿ (ℕtoℤ n) X)
-- Ωⁿ (neg       _ ) X = X -- TODO 

Ωⁿ : ℕ → Set₊ ℓ → Set₊ ℓ
Ωⁿ  zero    X = X  
Ωⁿ (succ n) X = Ω (Ωⁿ n X)



