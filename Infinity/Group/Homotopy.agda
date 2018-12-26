{-# OPTIONS --cubical --safe #-}

module Infinity.Group.Homotopy where

open import Infinity.Sigma
open import Infinity.Proto
open import Infinity.Path
open import Infinity.HIT.S1

Set₊ : Set
Set₊ = Σ[ A ∈ Set ] A

∣_∣ : Set₊ → Set
∣_∣ = π⃐

pt : (A : Set₊) → ∣ A ∣
pt = π⃑

Ω : Set₊ → Set₊
--Ω X = (S¹ → X , base → (pt X))
Ω X = X

Map₊ : Set₊ → Set₊ → Set
Map₊ A B = Σ[ f ∈ (∣ A ∣ → ∣ B ∣) ] (f (pt A) ≡ (pt B))

record Ω-Spectrum : Set where
  constructor _⋊_
  field
    spect : (n : ℕ) → Set₊
    chain : (n : ℕ) → (spect n) ≡ (Ω (spect (succ n)))
open Ω-Spectrum

record Ω-Map (E F : Ω-Spectrum) : Set where
  field
    mp : (n k : ℕ) → Map₊ (spect E n) (spect F (n + k))
open Ω-Map

