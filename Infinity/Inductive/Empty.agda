module Infinity.Inductive.Empty where

data ⊥ : Set where

ex-falso-quodlibet : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
ex-falso-quodlibet ()

infix 3 ¬_
¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

