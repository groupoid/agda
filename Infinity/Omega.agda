{-# OPTIONS --cubical --safe #-}

module Infinity.Omega where 

open import Infinity.Proto
open import Infinity.Trunc 
open import Infinity.Pointed

Ω : Set₊ → Set₊
-- Ω X = (S¹ → X , base → (pt X))
Ω X = X 
