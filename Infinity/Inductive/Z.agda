{-# OPTIONS --cubical --safe #-}

module Infinity.Inductive.Z where

open import Infinity.Proto renaming (_+_ to _+ℕ_)
open import Infinity.Sigma
open import Infinity.Path
open import Infinity.Equiv
open import Infinity.Univ

data ℤ : Set where
  pos : (n : ℕ) → ℤ
  neg : (n : ℕ) → ℤ
  
ℤtoℕ : ℤ → ℕ
ℤtoℕ (pos n) = n
ℤtoℕ (neg n) = n

ℕtoℤ : ℕ → ℤ
ℕtoℤ  zero    = pos zero
ℕtoℤ (succ n) = pos n

sucℤ : ℤ → ℤ
sucℤ (pos       n ) = pos (succ n)
sucℤ (neg  zero   ) = pos zero
sucℤ (neg (succ n)) = neg n

predℤ : ℤ → ℤ
predℤ (pos  zero   ) = neg zero
predℤ (pos (succ n)) = pos n
predℤ (neg       n ) = neg (succ n)

sucPred : (i : ℤ) → sucℤ (predℤ i) ≡ i
sucPred (pos  zero   ) = refl
sucPred (pos (succ n)) = refl
sucPred (neg  zero   ) = refl
sucPred (neg (succ n)) = refl

predSuc : (i : ℤ) → predℤ (sucℤ i) ≡ i
predSuc (pos  zero   ) = refl
predSuc (pos (succ _)) = refl
predSuc (neg  zero   ) = refl
predSuc (neg (succ _)) = refl

negate : ℤ → ℤ 
negate (pos  zero   ) = neg zero
negate (pos (succ n)) = neg n
negate (neg       n ) = pos (succ n)

_⊖_ : ℕ → ℕ → ℤ
n        ⊖  zero    = pos n 
zero     ⊖ (succ m) = neg (succ m)
(succ n) ⊖ (succ m) = n ⊖ m

_+_ : ℤ → ℤ → ℤ 
(pos n) + (pos m) = pos (n +ℕ m)
(pos n) + (neg m) = n ⊖ (succ m)
(neg n) + (pos m) = m ⊖ (succ n)
(neg n) + (neg m) = neg (succ (n +ℕ m))

_-_ : ℤ → ℤ → ℤ
n - m = n + (negate m)

0ℤ : ℤ
0ℤ = pos zero

1ℤ : ℤ
1ℤ = pos (succ zero)

2ℤ : ℤ
2ℤ = pos (succ (succ zero))

suc-equiv : ℤ ≃ ℤ
suc-equiv .π⃐ = sucℤ
suc-equiv .π⃑ = isoToIsEquiv sucℤ predℤ sucPred predSuc

sucPathInt : ℤ ≡ ℤ
sucPathInt = ua suc-equiv

-- module _ {A : Set ℓ₁} {B : Set ℓ₂} where 
--   π⃐≠π⃑ : (a : A) (b : B) (h : PathP (A + B) (π⃐ a) (π⃑ b)) → ⊥ 
--   π⃐≠π⃑ a b h = subst (A + B) ψ (π⃐ a) (π⃑ b) h unit
--     where ψ : A + B → Set (ℓ₁ ⊔ ℓ₂)
--           ψ (π⃐ _) = ⊤
--           ψ (π⃑ _) = ⊥
