{-# OPTIONS --cubical --safe #-}

module Infinity.Category.Monad where

open import Infinity.Proto

record Monad (m : Set ℓ → Set ℓ) : Set (ℓ-succ ℓ) where
  field 
    return : ∀ {a : Set ℓ} → a → m a 
    bind : ∀ {a b : Set ℓ} → (a → m b) → m a → m b
    
