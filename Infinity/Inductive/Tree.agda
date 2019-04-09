{-# OPTIONS --cubical --safe #-}

module Infinity.Inductive.Tree where 

open import Infinity.Proto

data Tree (A : Set ℓ) : Set ℓ where 
  lf :      A          → Tree A 
  nd : Tree A → Tree A → Tree A 
  
tr₁ : Tree ℕ
tr₁ = nd (lf 0) (lf 1)

tr₂ : Tree ℕ
tr₂ = nd (nd (lf 2) (lf 3)) tr₁

data Treesecta (A : Set ℓ) : ℕ → Set ℓ where 
  pt : A → Treesecta A 0 
  lf : {n : ℕ} → Treesecta A (succ n)
  nd : {n : ℕ} → A → Treesecta (Treesecta A (succ n)) n → Treesecta A (succ n)
  
data Stabilized (A : Set ℓ) : Set ℓ where 
  lf : Stabilized A 
  nd : A → Stabilized (Stabilized A) → Stabilized A 
  
spt : ∀ {A : Set ℓ} → A → Stabilized A 
spt a = nd a lf 

-- {-# TERMINATING #-}
-- -- _→ˢ_ : ∀ {A : Set ℓ} {a : A} {B : A → Set ℓ} (f : (a : A) → B a) → Stabilized A → Stabilized (B a)
-- _→ˢ_ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) → Stabilized A → Stabilized B
-- f →ˢ lf = lf 
-- f →ˢ (nd a sh) = nd (f a) ((_→ˢ_ f) →ˢ sh)
