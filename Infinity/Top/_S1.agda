{-# OPTIONS --cubical --rewriting #-}

module Infinity.Top.S1 where 

open import Infinity.Proto
open import Infinity.Z

postulate 
  S¹     : Set 
  base   : S¹ 
  loop   : base ≡ base 
  
loopS¹ : Set 
loopS¹ = base ≡ base 

invloop : base ≡ base 
invloop = λ i → loop (~ i)

_∘S¹_ : loopS¹ → loopS¹ → loopS¹ 
_∘S¹_ = transp

module S¹-Elim {ℓ : Level} {P : S¹ → Set ℓ} (base* : P base) (loop* : PathP (λ i → P (loop i)) base* base*) where 
  postulate S¹-elim : ∀ x → P x 
open S¹-Elim public


oneTurn : ∀ {l : loopS¹} → loopS¹
oneTurn {l = l} = l ∘S¹ loop

invTurn : ∀ {l : loopS¹} → loopS¹
invTurn {l = l} = l ∘S¹ invloop

loop̂⁻¹ᵢ : ℕ → loopS¹
loop̂⁻¹ᵢ zero = invloop
loop̂⁻¹ᵢ (suc n) = invTurn {l = loop̂⁻¹ᵢ n}

-- helix : S¹ → Set 
-- helix = S¹-elim ℤ sucPathℤ

π₁S¹ : Set 
π₁S¹ = base ≡ base 

-- winding : base ≡ base → ℤ
-- winding p = coe (λ i → helix (p i)) (pos zero)

-- TODO : defined previously
natLoop : ℕ → base ≡ base 
natLoop zero    = refl 
natLoop (suc n) = transp (natLoop n) loop

intLoop : ℤ → base ≡ base 
intLoop (pos    n) = natLoop n 
intLoop (negsuc n) = sym (natLoop (suc n))

