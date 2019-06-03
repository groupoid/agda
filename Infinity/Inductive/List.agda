{-# OPTIONS --cubical --safe #-}

module Infinity.Inductive.List where 

open import Infinity.Proto

infixr 50 _∷_

data List (A : Set ℓ) : Set ℓ where 
  [] : List A
  _∷_ : A → List A → List A 
  
{-# BUILTIN LIST List #-}

length : ∀ {A : Set ℓ} → List A → ℕ 
length [] = 0 
length (_ ∷ t) = 1 + length t 




-- Van Larhooven's approach to time complexity monad just by indexing 
module TC where
  infix 1 _in-time_
  data _in-time_ (A : Set ℓ) (n : ℕ) : Set ℓ where
    □ : A → A in-time n
    
open TC public using (_in-time_)
open TC

□-out : ∀ {A : Set ℓ} {n} → A in-time n → A
□-out (□ x) = x




-- TODO : separated monad instance
infixl 1 _>>=_
_>>=_ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → {n m : ℕ} → A in-time n → (A → B in-time m) → B in-time (n + m)
□ x >>= f = □ (□-out (f x))

return : ∀ {A : Set ℓ} → {n : ℕ} → A → A in-time n
return = □

-- TODO : separated functor instance 
infixr 2 _<$>_
_<$>_ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → {n : ℕ} → (A → B) → A in-time n → B in-time n
f <$> □ x = □ (f x)


-- bound-≡ : ∀ {a} {A : Set a} {m n} → (m ≡ n) → A in-time m → A in-time n
-- -- bound-≡ = PE.subst (_in-time_ _)

-- bound-+ : ∀ {a} {A : Set a} {m n k} → (m + k ≡ n) → A in-time m → A in-time n
-- bound-+ eq x = bound-≡ eq (x >>= return)

-- bound-≤ : ∀ {a} {A : Set a} {m n} → (m ≤ n) → A in-time m → A in-time n
-- bound-≤ m≤n = bound-+ (lem m≤n)
--   where
--   lem : ∀ {m n} → (m ≤ n) → m + (n ∸ m) ≡ n
--   lem z≤n        = PE.refl
--   lem (s≤s m≤n') = PE.cong suc (lem m≤n')

-- bound-≤′ : ∀ {a} {A : Set a} {m n} → (m ≤′ n) → A in-time m → A in-time n
-- bound-≤′ ≤′-refl     x = x
-- bound-≤′ (≤′-step l) x = return {n = 1} x >>= bound-≤′ l
