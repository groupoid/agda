{-# OPTIONS --cubical #-}

module Infinity.Algebra.Homology where

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Inductive.Z
open import Infinity.Algebra.Base
open import Infinity.Algebra.Kernel
open import Infinity.Algebra.Image
open import Infinity.Algebra.Chain 
-- open import Infinity.Algebra.Group.Quotient

module _ (c : C ℓ) where 
  private 
    module C = ChainComplex c
  
  abstract 
    Hₙ : ℤ → Group (ℓ-succ ℓ)
    Hₙ (pos zero) = Kernel.Ker (C.β zero) /ᴳ {!!} -- Image.Im (π⃑ (C.idx zero))
    Hₙ (pos (succ n)) = Kernel.Ker (C.β n) /ᴳ {!!} -- Image.Im (π⃑ (C.seq (succ n)))
    Hₙ (neg _) = 0ᴳ ↑ᴳ 
