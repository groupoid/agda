{-# OPTIONS --cubical #-}

module Infinity.Inductive.Opetope where 

open import Infinity.Proto 
open import Infinity.Inductive.One
open import Infinity.Inductive.List
open import Infinity.Inductive.Tree

Address : ℕ → Set ℓ 
Address 0 = ⊤
Address (succ n) = List (Address n)

data Addressˢ : Set where 
  dir : List Addressˢ → Addressˢ

data Nesting (A : Set ℓ) : Set ℓ where 
  ⋆ : A → Nesting A 
  ⊠ : A → Stabilized (Nesting A) → Nesting A 
  
Complex : (A : Set ℓ) → Set ℓ
Complex A = List (Nesting A)
