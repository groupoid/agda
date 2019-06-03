{-# OPTIONS --cubical --safe #-}

module Infinity.Category.Comonad where

open import Infinity.Proto
open import Infinity.Sigma
-- open import Infinity.Inductive.Nat


-- record IsComonad {W : Set → Set}
--        (extract : ∀ {A}   →  W A → A)
--        (extend  : ∀ {A B} → (W A → B) → W A → W B) : Set₁ where
--   field
--     extract-idʳ : ∀ {A} (x : W A) →
--       extend extract x ≡ x
--     extract-idˡ : ∀ {A B} (f : W A → B) (x : W A) →
--       extract (extend f x) ≡ f x
--     extend-asso : ∀ {A B C} (f : W B → C) (g : W A → B) (x : W A) →
--       extend f (extend g x) ≡ extend (f ∘ extend g) x

record Comonad (w : Set ℓ → Set ℓ) : Set (ℓ-succ ℓ) where
  field
    extract : ∀ {a : Set ℓ} → w a → a
    extend  : ∀ {a b : Set ℓ} → (w a → b) → w a → w b 
   -- isComonad : IsComonad extract extend
   
-- n-Comonad : ℕ → Set ℓ → Set (ℓ-succ ℓ)
-- n-Comonad 0 A = A
-- n-Comonad (succ n) A = Comonad (n-Comonad n A)

  -- open IsComonad isComonad public
