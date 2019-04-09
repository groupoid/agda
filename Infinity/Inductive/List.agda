{-# OPTIONS --cubical --safe #-}

module Infinity.Inductive.List where 

open import Infinity.Proto

infixr 50 _∷_

data List (A : Set ℓ) : Set ℓ where 
  [] : List A
  _∷_ : A → List A → List A 
  
{-# BUILTIN LIST List #-}

length : ∀ {A : Set ℓ} → List A → ℕ 
length [] = 0 
length (_ ∷ t) = 1 + length t 


