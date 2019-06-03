{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Quandle where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Algebra.Group
open import Infinity.Algebra.Rack

record Quandle-Skeleton (R : Set ℓ) : Set (ℓ-succ ℓ) where
  constructor quandle-skeleton
  
  field 
    skeleton : Rack-Skeleton R 

  -- field 
  --   reflt    : ∀ {a : R} → a Rack-Skeleton.◅ a ≡ a 
    
record Quandle ℓ : Set (ℓ-succ ℓ) where
  constructor qua
  field 
    Q : Set ℓ
    Skeleton : Quandle-Skeleton Q
    
TODO : group is quandle
