{-# OPTIONS --cubical --rewriting #-}

module Infinity.Top.S1 where

open import Infinity.Proto

data S¹ : Set where
  base : S¹
  loop : base ≡ base

ΩS¹ : Set
ΩS¹ = typeof loop


