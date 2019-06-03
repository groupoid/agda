{-# OPTIONS --cubical --no-exact-split --safe #-}

module Infinity.Inductive.Nat where

open import Infinity.Core
open import Infinity.Proto
open import Infinity.Inductive.Empty
open import Infinity.Inductive.Either
open import Infinity.Path
open import Infinity.HIT.NType
-- open import Infinity.Top.Space

predℕ : ℕ → ℕ
predℕ  zero    = 0
predℕ (succ n) = n

ℕ-rec : ∀ {A : Set ℓ} (a₀ aₛ : A) → ℕ → A
ℕ-rec a₀ _        0  = a₀
ℕ-rec _  aₛ (succ _) = aₛ

_^_ : ℕ → ℕ → ℕ
_ ^ zero   = 1
x ^ succ n = x * (x ^ n)

z¬s : ∀ {n : ℕ} → ¬ (0 ≡ succ n)
z¬s eq = subst (ℕ-rec ℕ ⊥) eq 0

s¬z : ∀ {n : ℕ} → ¬ (succ n ≡ 0)
s¬z eq = subst (ℕ-rec ⊥ ℕ) eq 0

injSuc : ∀ {m n : ℕ} → succ m ≡ succ n → m ≡ n
injSuc = cong predℕ 

doubleℕ : ℕ → ℕ
doubleℕ       0  = 0
doubleℕ (succ x) = succ (succ (doubleℕ x))

-- doublesℕ n m = 2^n * m
doublesℕ : ℕ → ℕ → ℕ
doublesℕ       0  m = m
doublesℕ (succ n) m = doublesℕ n (doubleℕ m)

-- 1024 = 2^8 * 2^2 = 2^10
n1024 : ℕ
n1024 = doublesℕ 8 4

iter : ∀ {A : Set ℓ} → ℕ → (A → A) → A → A
iter  zero    _ z = z
iter (succ n) f z = f (iter n f z)

-- discreteℕ : discrete ℕ
-- discreteℕ  zero     zero    = inl refl
-- discreteℕ  zero    (succ _) = inr z¬s
-- discreteℕ (succ _)  zero    = inr s¬z
-- discreteℕ (succ m) (succ n) with discreteℕ m n
-- ...                       | inl p = inl (cong succ p)
-- ...                       | inr p = inr (λ x → p (injSuc x))

-- isSetℕ : isSet ℕ
-- isSetℕ = discrete→isSet discreteℕ

1+m+n=m+1+n : (m n : ℕ) → succ (m + n) ≡ m + succ n
1+m+n=m+1+n  zero    _ = refl
1+m+n=m+1+n (succ m) n = cong succ (1+m+n=m+1+n m n)



-- module Logarithm where
