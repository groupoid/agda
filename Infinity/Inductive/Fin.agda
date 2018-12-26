module Infinity.Inductive.Fin where

open import Infinity.Proto

data Fin : ℕ → Set where
  fz : {n : ℕ} → Fin (succ n)
  fs : {n : ℕ} (i : Fin n) → Fin (succ n)

toℕ : ∀ {n} → Fin n → ℕ
toℕ fz    = zero
toℕ (fs i) = succ (toℕ i)

fromℕ : (n : ℕ) → Fin (succ n)
fromℕ zero    = fz
fromℕ (succ n) = fs (fromℕ n)

