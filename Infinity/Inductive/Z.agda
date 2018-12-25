{-# OPTIONS --cubical --safe #-}
module Infinity.Inductive.Z where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Equiv
open import Infinity.Univ

data ℤ : Set where
  pos    : (n : ℕ) → ℤ
  negsuc : (n : ℕ) → ℤ

sucℤ : ℤ → ℤ
sucℤ (pos n)          = pos (suc n)
sucℤ (negsuc zero)    = pos zero
sucℤ (negsuc (suc n)) = negsuc n

predℤ : ℤ → ℤ
predℤ (pos zero)      = negsuc zero
predℤ (pos (suc n))   = pos n
predℤ (negsuc n)      = negsuc (suc n)

sucPred : ∀ i → sucℤ (predℤ i) ≡ i
sucPred (pos zero)       = refl
sucPred (pos (suc n))    = refl
sucPred (negsuc zero)    = refl
sucPred (negsuc (suc n)) = refl

predSuc : ∀ i → predℤ (sucℤ i) ≡ i
predSuc (pos zero)       = refl
predSuc (pos (suc n))    = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

oneℤ : ℤ 
oneℤ = pos (suc zero)

twoℤ : ℤ
twoℤ = pos (suc (suc zero))

suc-equiv : ℤ ≃ ℤ
suc-equiv .π⃐ = sucℤ
suc-equiv .π⃑ = isoToIsEquiv sucℤ predℤ sucPred predSuc

sucPathInt : ℤ ≡ ℤ
sucPathInt = ua suc-equiv
