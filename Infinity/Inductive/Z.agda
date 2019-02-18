{-# OPTIONS --cubical --safe #-}

module Infinity.Inductive.Z where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Equiv
open import Infinity.Univ

data ℤ : Set where
  pos    : (n : ℕ) → ℤ
  neg : (n : ℕ) → ℤ

ℤtoℕ : ℤ → ℕ
ℤtoℕ (pos    n) = n
ℤtoℕ (neg n) = n

ℕtoℤ : ℕ → ℤ
ℕtoℤ zero     = pos zero
ℕtoℤ (succ n) = pos n

sucℤ : ℤ → ℤ
sucℤ (pos n)        = pos (succ n)
sucℤ (neg zero)     = pos zero
sucℤ (neg (succ n)) = neg n

predℤ : ℤ → ℤ
predℤ (pos zero)     = neg zero
predℤ (pos (succ n)) = pos n
predℤ (neg n)        = neg (succ n)

sucPred : ∀ i → sucℤ (predℤ i) ≡ i
sucPred (pos zero)     = refl
sucPred (pos (succ n)) = refl
sucPred (neg zero)     = refl
sucPred (neg (succ n)) = refl

predSuc : ∀ i → predℤ (sucℤ i) ≡ i
predSuc (pos zero)     = refl
predSuc (pos (succ n)) = refl
predSuc (neg zero)     = refl
predSuc (neg (succ n)) = refl

zeroℤ : ℤ
zeroℤ = pos zero

oneℤ : ℤ
oneℤ = pos (succ zero)

twoℤ : ℤ
twoℤ = pos (succ (succ zero))

suc-equiv : ℤ ≃ ℤ
suc-equiv .π⃐ = sucℤ
suc-equiv .π⃑ = isoToIsEquiv sucℤ predℤ sucPred predSuc

sucPathInt : ℤ ≡ ℤ
sucPathInt = ua suc-equiv
