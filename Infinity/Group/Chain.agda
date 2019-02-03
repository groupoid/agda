{-# OPTIONS --cubical --safe #-}

module Infinity.Group.Chain where 

open import Infinity.Proto
open import Infinity.Inductive.Z 
open import Infinity.Group.Homomorphism
open import Infinity.Group.Base
open import Infinity.Group.Abelian

record ChainComplex ℓ : Set (ℓ-succ ℓ) where
  field
    seq  : Abᴳ ℓ
    idx : ℕ → Abᴳ ℓ
    aug : Abᴳ.grp (idx zero) →ᴳ Abᴳ.grp seq
    β   : ∀ n → (Abᴳ.grp (idx (succ n)) →ᴳ Abᴳ.grp (idx n))

C = ChainComplex

-- record ChainComplexAugmented (I : Group ℓ) : Set (ℓ-succ ℓ) where 
--   field 
--     seq  : Abᴳ ℓ
--     idx  : ℕ → Abᴳ ℓ
--     aug : Abᴳ.grp (idx zero) →ᴳ Abᴳ.grp hd
--     coe : ∀ n → Abᴳ.grp (idx (succ n)) →ᴳ I →ᴳ Abᴳ.grp (idx n)
--     β   : ∀ n → Abᴳ.grp (idx (succ n)) →ᴳ Abᴳ.grp (idx n)

record CochainComplex ℓ : Set (ℓ-succ ℓ) where
  field 
    seq : Abᴳ ℓ
    idx : ℕ → Abᴳ ℓ
    aug : Abᴳ.grp seq →ᴳ Abᴳ.grp (idx zero) 
    δ   : ∀ n → Abᴳ.grp (idx n) →ᴳ Abᴳ.grp (idx (succ n))

C* = CochainComplex

