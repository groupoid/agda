module Infinity.Inductive.Empty where

data ⊥ : Set where

efq : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
efq ()

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

