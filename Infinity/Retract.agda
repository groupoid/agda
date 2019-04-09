{-# OPTIONS --cubical --safe #-}

module Infinity.Retract where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Univ
open import Infinity.Equiv
open import Infinity.HIT.NType

module _ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (g : B → A) where
  section : Set ℓ₂
  section = ∀ b → f (g b) ≡ b
  
  retract : Set ℓ₁
  retract = ∀ a → g (f a) ≡ a
  
  lemRetract : (r : retract) (x y : A) (p : g (f x) ≡ g (f y)) → x ≡ y
  lemRetract r x y p = comp↑ {_} {_} {(g (f x))} {x} {(g (f y))} {y} (r x) (r y) p

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
  
≃→≡ : ∀ {A B : Set ℓ} (f : A → B) (g : B → A) (s : section f g) (t : retract f g) → A ≡ B 
≃→≡ {_} {A} {B} f g s t = λ i → Glue B (λ { (i = i0) → _ , isoToEquiv f g s t 
                                          ; (i = i1) → _ , _ , idIsEquiv B })

-- private 
  -- ≃→≡-ex : ∀ {A B : Set ℓ} (f : A → B) (g : B → A) (s : section f g) (t : retract f g) (a : A) 
         -- → f a ≡ trans (isoPath f g s t) a  
  -- ≃→≡-ex f g s t a = λ i → comp B (λ { (i = i0) → λ _ → f a }) (comp B (λ { (i = i0) → λ _ → f a }) (f a))

module _ {A : Set ℓ₁} {B : A → Set ℓ₂} where 
    -- TODO : Beautiful case for beautiful combinators 
    Σ-≡ : (t u : Σ A B) → (t ≡ u) ≡ (Σ[ p ∈ (π⃐ t ≡ π⃐ u) ] PathP (λ i → B (p i)) (π⃑ t) (π⃑ u))
    Σ-≡ t u = ≃→≡ f g (λ p → refl {x = p}) (λ q → refl {x = q})
      where T₁ : Set (ℓ₁ ⊔ ℓ₂)
            T₁ = t ≡ u 
            T₂ : Set (ℓ₁ ⊔ ℓ₂)
            T₂ = Σ[ p ∈ (π⃐ t ≡ π⃐ u) ] PathP (λ i → B (p i)) (π⃑ t) (π⃑ u)
            f : (q : T₁) → T₂ 
            f q .π⃐ i = π⃐ (q i) 
            f q .π⃑ i = π⃑ (q i)
            g : (p : T₂) → T₁
            g p i .π⃐ = (π⃐ p) i 
            g p i .π⃑ = (π⃑ p) i
            
    Σ-entwine : (t u : Σ A B) (p : π⃐ t ≡ π⃐ u) (q : PathP (λ i → B (p i)) (π⃑ t) (π⃑ u)) → t ≡ u
    Σ-entwine t u p q = coe (sym (Σ-≡ t u)) (p , q)
