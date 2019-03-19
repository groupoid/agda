{-# OPTIONS --cubical --safe #-}

module Infinity.Retract where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Equiv
open import Infinity.HIT.NType

module _ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (g : B → A) where
  section : Set ℓ₂
  section = ∀ b → f (g b) ≡ b
  
  retract : Set ℓ₁
  retract = ∀ a → g (f a) ≡ a
  
  lemRetract : (r : retract) (x y : A) (p : g (f x) ≡ g (f y)) → x ≡ y
  lemRetract r x y p = comp↑ (g (f x)) x (g (f y)) y (r x) (r y) p

  retractProp : (r : retract) (pb : isProp B) → isProp A
  retractProp r pb x y = lemRetract r x y (cong g (pb (f x) (f y)))

  retract⁻¹ : (r : retract) (x y : A) (q : f x ≡ f y) → x ≡ y
  retract⁻¹ r x y q = lemRetract r x y (cong g q) 
  
  -- lemR□ : (r : retract) (x y : A) (p : x ≡ y) → Square (g (f x)) (g (f y)) (λ i → g (f (p i))) x y 
  -- lemR□ r x y p = λ i j → primComp A _ (λ { (j = i0) → λ l → (r x) (i ∧ l) ; (j = i1) → λ l (rfg y) (i ∧ l) }) (g (f (p j))) 
  
  -- retract≡ (r : retract) (x y : A) (p : x ≡ y) → (x ≡ y) ≡ (retract⁻¹ r x y (λ i → f (p i)))
  -- retract≡ r x y p = λ i j → primComp A (λ { (j = i0) →       r x       ; (j = i1) → r y 
  --                                          ; (i = i0) → lemR□ r x y p j ; (i = i1) → r (p j) }) (g (f (p j)))
  
module _ {A : Set ℓ₁} {B : Set ℓ₂} where
  HasSection : (f : A → B) → Set (ℓ₁ ⊔ ℓ₂)
  HasSection f = Σ[ g ∈ (B → A) ] retract g f
  
  IsRetract : Set (ℓ₁ ⊔ ℓ₂)
  IsRetract = Σ (A → B) HasSection
  
  retract₋₂ : IsRetract → isContr A → isContr B
  retract₋₂ (r , _ , _) (a , _    ) .π⃐ = r a 
  retract₋₂ (r , s , ε) (_ , contr) .π⃑ = λ b → trans (sym (cong r (sym (contr (s b))))) (ε b)

  retract₋₁ : IsRetract → isProp A → isProp B 
  retract₋₁ (r , s , ε) = retractProp s r ε 

  -- retract≃ : A ≃ B → IsRetract 
  -- retract≃ (f , e) .π⃐ = f 
  -- retract≃ (f , e) .π⃑ .π⃐ = λ b → π⃐ (π⃐ (e b))
  -- retract≃ (f , e) .π⃑ .π⃑ = λ b → sym (π⃑ (π⃐ e b))
