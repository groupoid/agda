{-# OPTIONS --cubical --safe #-}

module Infinity.Graph where 

open import Agda.Builtin.List public
  using (List; []; _∷_)

open import Infinity.Proto 
open import Infinity.Sigma

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (succ n)
  succ : {n : ℕ} (i : Fin n) → Fin (succ n)

record Context {ℓ₁ ℓₑ} (Node : Set ℓ₁) (Edge : Set ℓₑ) (n : ℕ) : Set (ℓ₁ ⊔ ℓₑ) where 
  constructor context 
  field 
    label      : Node 
    successors : List (Edge × Fin n)
    
open Context 

module _ {ℓ₁ e₁} {N₁ : Set ℓ₁} {E₁ : Set e₁}
         {ℓ₂ e₂} {N₂ : Set ℓ₂} {E₂ : Set e₂} where
  cmap : ∀ {n : ℕ} → (N₁ → N₂) → (List (E₁ × Fin n) → List (E₂ × Fin n)) → Context N₁ E₁ n → Context N₂ E₂ n
  cmap f g c = context (f (label c)) (g (successors c))

infixr 3 _&_

data Graph {ℓ ℓₑ} (Node : Set ℓ) (Edge : Set ℓₑ) : ℕ → Set (ℓ ⊔ ℓₑ) where
  ∅   : Graph Node Edge 0
  _&_ : ∀ {n} (c : Context Node Edge n) (g : Graph Node Edge n) → Graph Node Edge (succ n)
