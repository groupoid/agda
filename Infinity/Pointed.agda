{-# OPTIONS --cubical --type-in-type #-}

module Infinity.Pointed where 

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.One
open import Infinity.Top.S1

Set₊ : Set
Set₊ = Σ[ A ∈ Set ] A

∣_∣ : Set₊ → Set
∣_∣ = π⃐ 

pt : (A : Set₊) → ∣ A ∣
pt = π⃑

Map₊ : Set₊ → Set₊ → Set
Map₊ A B = Σ[ f ∈ (∣ A ∣ → ∣ B ∣) ] (f (pt A) ≡ (pt B))
