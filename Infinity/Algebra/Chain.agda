{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Chain where 

open import Infinity.Proto
open import Infinity.Inductive.Z 
open import Infinity.Algebra.Base

record ChainComplex ℓ : Set (ℓ-succ ℓ) where
  field
    seq  : Abelian ℓ
    idx : ℕ → Abelian ℓ
    aug : Abelian.grp (idx zero) →ᴳ Abelian.grp seq
    β   : ∀ n → (Abelian.grp (idx (succ n)) →ᴳ Abelian.grp (idx n))

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
    seq : Abelian ℓ
    idx : ℕ → Abelian ℓ
    aug : Abelian.grp seq →ᴳ Abelian.grp (idx zero) 
    δ   : ∀ n → Abelian.grp (idx n) →ᴳ Abelian.grp (idx (succ n))

C* = CochainComplex

