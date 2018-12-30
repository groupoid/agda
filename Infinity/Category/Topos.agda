{-# OPTIONS --cubical #-}

module Infinity.Category.Topos where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Category.Functor

Presheaf : Set (ℓ-succ ℓ)
Presheaf = Func
