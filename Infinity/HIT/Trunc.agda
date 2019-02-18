{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Infinity.HIT.Trunc where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.HIT.NType

data ∥_∥ (A : Set ℓ) : Set ℓ where
  ∣_∣    : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y

recPropTrunc : ∀ {A : Set ℓ} {P : Set ℓ} → isProp P → (A → P) → ∥ A ∥ → P
recPropTrunc _ f ∣ x ∣ = f x
recPropTrunc P f (squash x y i) = P (recPropTrunc P f x) (recPropTrunc P f y) i

propTruncIsProp : ∀ {A : Set ℓ} → isProp ∥ A ∥
propTruncIsProp = squash

elimPropTrunc : ∀ {A : Set ℓ} {P : ∥ A ∥ → Set ℓ} → ((a : ∥ A ∥) → isProp (P a)) → ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
elimPropTrunc PP f ∣ x ∣ = f x
elimPropTrunc {A = A} {P = P} PP f (squash x y i) = PPOver (squash x y) (elimPropTrunc PP f x) (elimPropTrunc PP f y) i where
  PPOver : {a b : ∥ A ∥} → (sq : a ≡ b) → ∀ x y → PathP (λ i → P (sq i)) x y
  PPOver {a} = J (λ b (sq : a ≡ b) → ∀ x y → PathP (λ i → P (sq i)) x y) (PP a)

elimPropTrunc' : ∀ {A : Set ℓ} {P : ∥ A ∥ → Set ℓ} → ((a : ∥ A ∥) → isProp (P a)) → ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
elimPropTrunc' {P = P} PP f a = recPropTrunc (PP a) (λ x → transp (λ i → P (squash ∣ x ∣ a i)) i0 (f x)) a

trunc-map : ∀ {n : ℕ} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (A → B → C) → isOfHLevel n A → isOfHLevel n B → isOfHLevel n C
trunc-map = {!!} -- rec λ a → map (f a)

