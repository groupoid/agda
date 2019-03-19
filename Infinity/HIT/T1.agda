{-# OPTIONS --cubical --safe #-}

module Infinity.HIT.T1 where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.HIT.S1

data T¹ : Set where 
  base  : T¹ 
  loop₁ : base ≡ base 
  loop₂ : base ≡ base 
  surf  : trans loop₁ loop₂ ≡ trans loop₂ loop₁

T¹' : Set 
T¹' = S¹ × S¹

-- T¹≡T¹' : T¹ ≡ T¹' 
-- T¹≡T¹' = {!!} -- λ i → primComp (λ _ → Set) _ (λ { (i = i1) → T¹→T¹' ; (i = i0) → T¹'→T¹ })


-- module T¹-Elim {P : T¹ → Set ℓ} (base* : P base) 
--                                 (loop₁* : PathP (λ i → P (loop₁ i)) base* base*)
--                                 (loop₂* : PathP (λ i → P (loop₂ i)) base* base*)
--                                 (surf : PathP (λ i → (λ p → PathP (λ j → p j) base* base*) (surf i)) 
--                                         (trans loop₁* loop₂*) (trans loop₂* loop₁*)) where
--   postulate T¹-elim : ∀ x → P x

-- open T¹-Elim public
                                
