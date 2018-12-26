module Infinity.Inductive.Either where

data _ω_ {l} (A B : Set l) : Set l where
  inl : A → A ω B
  inr : B → A ω B

either : ∀ {l} {A B C : Set l} → (A → C) → (B → C) → A ω B → C
either f g (inl x) = f x
either f g (inr x) = g x

