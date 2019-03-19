{-# OPTIONS --cubical #-}

module Infinity.Algebra.Homotopy where

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Omega
open import Infinity.Path
open import Infinity.HIT.S1
open import Infinity.HIT.Trunc hiding (∣_∣)
open import Infinity.Inductive.Z
open import Infinity.Algebra.Base 
open import Infinity.Algebra.Spectrum

-- πˢ : ℤ → Ω-Spectrum → Set ℓ
-- πˢ (pos       zero) E = ∥                  ∣ spect E zero ∣                ∥
-- πˢ (pos n@(succ _)) E = ∥ (n-path (succ n) ∣ spect E zero ∣ (bp (sp E Z))) ∥
-- πˢ (neg    zero   ) E = ∥                  ∣ spect E zero ∣                ∥
-- πˢ (neg n@(succ _)) E = ∥                  ∣ spect E n    ∣                ∥
