{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Rack where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Algebra.Group

record Rack-Skeleton (R : Set ℓ) : Set ℓ where
  constructor rack-skeleton
  field 
    _◅_ : R → R → R
    _▻_ : R → R → R 
    
    sdl : ∀ {a b c : R} → a ◅ (b ◅ c) ≡ (a ◅ b) ◅ (a ◅ c)
    sdr : ∀ {a b c : R} → (c ▻ b) ▻ a ≡ (c ▻ a) ▻ (b ▻ a)
    dlr : ∀ {a b c : R} → (a ◅ b) ▻ a ≡ b 
    
    sig : ∀ {a b : R} → Σ[ c ∈ R ] a ◅ c ≡ b
    
record Rack ℓ : Set (ℓ-succ ℓ) where
  constructor ⟦_,_⟧
  field 
    R : Set ℓ
    Skeleton : Rack-Skeleton R
    
