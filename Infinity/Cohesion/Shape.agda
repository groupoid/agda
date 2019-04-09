{-# OPTIONS --cubical --safe #-}

module Infinity.Cohesion.Shape where

open import Infinity.Proto

variable 𝔸 : Set

data #∫ (A : Set) : Set where 
    #σ  :  A → #∫ A
    #κ  : (𝔸 → #∫ A) → #∫ A
    #κ' : (𝔸 → #∫ A) → #∫ A

∫ : (A : Set) → Set 
∫ = #∫

module _ {A : Set} where 
    σ : A → ∫ A
    σ = #σ

    κ : (𝔸 → ∫ A) → ∫ A
    κ = #κ
