{-# OPTIONS --cubical --safe #-}

module Infinity.Fibration where 

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Reason

open import Agda.Builtin.Cubical.Glue using (isEquiv ; _≃_ ; equivFun)

open isEquiv using (equiv-proof)

module Fiber-Dep {A : Set ℓ₁} {B : A → Set ℓ₂} where 
  fiber : (f : (a : A) → B a) (y : ∀ {a : A} → B a) → Set (ℓ₁ ⊔ ℓ₂)
  fiber f y = Σ[ x ∈ A ] (f x ≡ y)
    where open import Infinity.Sigma using (Σ-syntax)

  fib : Σ A B → A 
  fib = π⃐

module Fiber {A : Set ℓ₁} {B : Set ℓ₂} where 
  fiber : (f : A → B) (y : B) → Set (ℓ₁ ⊔ ℓ₂)
  fiber f y = Σ[ x ∈ A ] (f x ≡ y)
    where open import Infinity.Sigma using (Σ-syntax)
    
  fib : A × B → A 
  fib = π⃐
        
  equivIsEquiv : (e : A ≃ B) → isEquiv (equivFun e)
  equivIsEquiv e = π⃑ e

  equivCtr : (e : A ≃ B) (y : B) → fiber (equivFun e) y
  equivCtr e y = e .π⃑ .equiv-proof y .π⃐

  equivCtrPath : (e : A ≃ B) (y : B) → (v : fiber (equivFun e) y) → Path _ (equivCtr e y) v
  equivCtrPath e y = e .π⃑ .equiv-proof y .π⃑
  
open Fiber public

fibration : ∀ ℓ₂ → Set ℓ₁ → Set _ 
fibration ℓ₂ A = Σ (Set ℓ₂) λ B → B → A

-- module Laws {A : Set ℓ₁} {B : A → Set ℓ₂} where 
--   fib-iso : (a : A) → fiber (fib {B = B}) a ≃ B a 
--   fib-iso a .π⃐ = λ f → {!!} -- (π⃑ f)
--   fib-iso a .π⃑ .equiv-proof a₁ .π⃐ = {!!}
--   fib-iso a .π⃑ .equiv-proof a₁ .π⃑ = {!!}
  

