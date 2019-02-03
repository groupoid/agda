{-# OPTIONS --cubical --safe #-}

module Infinity.Group.Homology where

open import Infinity.Proto
open import Infinity.Group.Kernel
open import Infinity.Group.Image
open import Infinity.Group.Chain 

-- Hₙ : C ℓ → ℤ → Group ℓ
-- Hₙ c (pos zero) = Ker (c.β zero) / Im (π⃑ (c.idx zero))
