{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Infinity.Fibration where 

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Univ
open import Infinity.Reason

open import Agda.Builtin.Cubical.Glue using (isEquiv ; _≃_ ; equivFun)

open isEquiv using (equiv-proof) public

module _ {A : Set ℓ₁} {B : A → Set ℓ₂} where 
    fiber : (f : (x : A) → B x) (y : ∀ {x : A} → B x) → Set (ℓ₁ ⊔ ℓ₂)
    fiber f y = Σ[ x ∈ A ] (f x ≡ y)

    fib : Σ A B → A 
    fib = π⃐
    
fibration : ∀ ℓ₂ → Set ℓ₁ → Set _ 
fibration ℓ₂ A = Σ (Set ℓ₂) λ B → B → A

module Laws {A : Set ℓ₁} {B : A → Set ℓ₂} where 
  fib-iso : (a : A) → fiber (fib {B = B}) a ≃ B a 
  fib-iso a .π⃐ = λ f → {!!} -- (π⃑ f)
  fib-iso a .π⃑ .equiv-proof a₁ .π⃐ = {!!}
  fib-iso a .π⃑ .equiv-proof a₁ .π⃑ = {!!}
  

