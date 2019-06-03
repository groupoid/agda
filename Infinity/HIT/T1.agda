{-# OPTIONS --cubical --safe #-}

module Infinity.HIT.T1 where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Univ
open import Infinity.Equiv
open import Infinity.Retract
open import Infinity.HIT.S1

data T¹ : Set where 
  base  : T¹ 
  loop₁ : base ≡ base 
  loop₂ : base ≡ base 
  -- surf  : trans loop₁ loop₂ ≡ trans loop₂ loop₁
  surf  : PathP (λ i → loop₁ i ≡ loop₁ i) loop₂ loop₂

T¹' : Set 
T¹' = S¹ × S¹

T¹→T¹' : T¹ → T¹' 
T¹→T¹'  base      = base   , base 
T¹→T¹' (loop₁  i) = loop i , base 
T¹→T¹' (loop₂  j) = base   , loop j
T¹→T¹' (surf i j) = loop i , loop j

T¹'→T¹ : T¹' → T¹
T¹'→T¹ (base   , base  ) = base
T¹'→T¹ (loop i , base  ) = loop₁   i
T¹'→T¹ (base   , loop j) = loop₂   j
T¹'→T¹ (loop i , loop j) = surf  i j

T¹→T¹'-T¹'→T¹ : section T¹→T¹' T¹'→T¹
T¹→T¹'-T¹'→T¹ (base   , base  ) = refl
T¹→T¹'-T¹'→T¹ (base   , loop _) = refl
T¹→T¹'-T¹'→T¹ (loop _ , base  ) = refl
T¹→T¹'-T¹'→T¹ (loop _ , loop _) = refl

T¹'→T¹-T¹→T¹' : retract T¹→T¹' T¹'→T¹
T¹'→T¹-T¹→T¹'  base       = refl
T¹'→T¹-T¹→T¹' (loop₁   _) = refl
T¹'→T¹-T¹→T¹' (loop₂   _) = refl
T¹'→T¹-T¹→T¹' (surf  _ _) = refl

T¹≡T¹' : T¹ ≡ T¹' 
T¹≡T¹' = ≃→≡ T¹→T¹' T¹'→T¹ T¹→T¹'-T¹'→T¹ T¹'→T¹-T¹→T¹'


-- module T¹-Elim {P : T¹ → Set ℓ} (base* : P base) 
--                                 (loop₁* : PathP (λ i → P (loop₁ i)) base* base*)
--                                 (loop₂* : PathP (λ i → P (loop₂ i)) base* base*)
--                                 (surf : PathP (λ i → (λ p → PathP (λ j → p j) base* base*) (surf i)) 
--                                         (trans loop₁* loop₂*) (trans loop₂* loop₁*)) where
--   postulate T¹-elim : ∀ x → P x

-- open T¹-Elim public
                                
