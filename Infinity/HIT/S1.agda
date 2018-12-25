{-# OPTIONS --cubical --rewriting #-}
module Infinity.HIT.S1 where

open import Infinity.Core
open import Infinity.Proto
open import Infinity.Path public
open import Infinity.Inductive.Z

data S¹ : Set where
   base : S¹
   loop : base ≡ base

ΩS¹ : Set
ΩS¹ = base ≡ base

helix : S¹ → Set
helix base     = ℤ
helix (loop i) = sucPathInt i

loopS¹ : Set 
loopS¹ = base ≡ base 

invloop : base ≡ base 
invloop = λ i → loop (~ i)

module S¹-Elim {ℓ : Level} {P : S¹ → Set ℓ} (base* : P base) (loop* : PathP (λ i → P (loop i)) base* base*) where 
  postulate S¹-elim : ∀ x → P x 

open S¹-Elim public

π₁S¹ : Set 
π₁S¹ = base ≡ base 

