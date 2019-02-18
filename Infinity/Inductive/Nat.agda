{-# OPTIONS --cubical --no-exact-split #-}

module Infinity.Inductive.Nat where

open import Infinity.Core
open import Infinity.Proto
open import Infinity.Inductive.Empty
open import Infinity.Inductive.Either
open import Infinity.Path
open import Infinity.HIT.NType
open import Infinity.Top.Space

predℕ : ℕ → ℕ
predℕ zero    = 0
predℕ (succ n) = n

caseNat : ∀{l} → {A : Set l} → (a0 aS : A) → ℕ → A
caseNat a0 aS 0       = a0
caseNat a0 aS (succ n) = aS

znots : {n : ℕ} → ¬ (0 ≡ succ n)
znots eq = subst (caseNat ℕ ⊥) eq 0

snotz : {n : ℕ} → ¬ (succ n ≡ 0)
snotz eq = subst (caseNat ⊥ ℕ) eq 0

injSuc : {m n : ℕ} → succ m ≡ succ n → m ≡ n
injSuc p = cong predℕ p

doubleℕ : ℕ → ℕ
doubleℕ 0 = 0
doubleℕ (succ x) = succ (succ (doubleℕ x))

-- doublesℕ n m = 2^n * m
doublesℕ : ℕ → ℕ → ℕ
doublesℕ 0 m = m
doublesℕ (succ n) m = doublesℕ n (doubleℕ m)

-- 1024 = 2^8 * 2^2 = 2^10
n1024 : ℕ
n1024 = doublesℕ 8 4

-- iterate
iter : {A : Set} → ℕ → (A → A) → A → A
iter zero f z    = z
iter (succ n) f z = f (iter n f z)

discreteℕ : discrete ℕ
discreteℕ zero zero = inl refl
discreteℕ zero (succ n) = inr znots
discreteℕ (succ m) zero = inr snotz
discreteℕ (succ m) (succ n) with discreteℕ m n
... | inl p = inl (cong succ p)
... | inr p = inr (λ x → p (injSuc x))

isSetℕ : isSet ℕ
isSetℕ = discrete→isSet discreteℕ
