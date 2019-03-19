{-# OPTIONS --cubical --allow-unsolved-metas --omega-in-omega #-}

module Infinity.Algebra.Cohomology where 

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Omega
open import Infinity.HIT.Trunc
open import Infinity.HIT.NType
open import Infinity.Inductive.Z
open import Infinity.Inductive.One
open import Infinity.Algebra.Base
open import Infinity.Algebra.Chain
open import Infinity.Algebra.Kernel
open import Infinity.Algebra.Image
open import Infinity.Algebra.Homomorphism
open import Infinity.Algebra.Group.Quotient


module Canonical (C : C* ℓ) where
  private 
    module C = CochainComplex C 
    
  abstract 
    Hⁿ : ℤ → Group (ℓ-succ ℓ)
    Hⁿ (pos 0) = Kernel.Ker (C.δ 0) /ᴳ {!!} -- (Image.Im (C.δ 1) ≡ 0ᴳ ↑ᴳ)
    Hⁿ (pos (succ n)) = Kernel.Ker (C.δ n) /ᴳ {!!} -- (Image.Im (C.δ (succ n)) ≡ 0ᴳ ↑ᴳ)
    Hⁿ (neg _) = 0ᴳ ↑ᴳ

module Synthetic where 
  abstract 
    Hⁿ : ℤ → Set ℓ → Set ℓ → Set (ℓ-succ ℓ)
    -- Hⁿ n X C = Σ[ k ∈ ℤ ] ∥ (λ X → Ωⁿ (k - n) ∣ Ω-Spectrum.spect (ℤtoℕ k) ∣) ∥
    Hⁿ n X C = {!!} -- Σ[ k ∈ ℤ ] ∥ (λ X → Ωⁿ (k - n) (isOfHLevel (ℤtoℕ k) C , unit)) ∥
