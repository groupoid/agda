{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Group.Magma where 

open import Infinity.Proto hiding (_∘_)
open import Infinity.Path
open import Infinity.Pointed

record Magma (A : Set ℓ) : Set ℓ where
  constructor magma 
  field 
    _·_ : A → A → A

record Magma₊ (A : Set ℓ) : Set ℓ where
  constructor magma₊
  field 
    _·_ : A → A → A 
    pt  : A 
