module Infinity.Inductive.Either where

data _ω_ {l} (A B : Set l) : Set l where
  left : A → A ω B
  right : B → A ω B

either : ∀ {l} {A B C : Set l} → (A → C) → (B → C) → A ω B → C
either f g (left x) = f x
either f g (right x) = g x

