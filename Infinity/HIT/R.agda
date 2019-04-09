{-# OPTIONS --cubical --safe #-}

module Infinity.HIT.R where 

open import Infinity.Proto 
open import Infinity.Inductive.Z

data ℝ : Set where 
  zero : ℤ → ℝ
  equi : (n : ℤ) → zero n ≡ zero (succℤ n)
