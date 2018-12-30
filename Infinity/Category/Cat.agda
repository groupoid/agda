{-# OPTIONS --cubical --safe #-}

module Infinity.Category.Cat where

open import Infinity.Proto
open import Infinity.Path

-- Enrich Set with categorical structure 
record Category {Ob : Set ℓ} (Hom : Ob → Ob → Set ℓ) : Set (ℓ-succ ℓ) where 
    field 
        id  : ∀ {A : Ob} → Hom A A
        _○_ : ∀ {A B C : Ob} → Hom A B → Hom B C → Hom A C 
        
        .{{lid}}   : ∀ {A B     : Ob} (f : Hom A B) → (id ○ f) ≡ f
        .{{rid}}   : ∀ {A B     : Ob} (f : Hom A B) → (f ○ id) ≡ f
        .{{assoc}} : ∀ {A B C D : Ob} (f : Hom A B) (g : Hom B C) (h : Hom C D) → ((f ○ g) ○ h) ≡ (f ○ (g ○ h))

_○ᵖ : ∀ {Ob} {Hom : Ob → Ob → Set ℓ} → Category Hom → Category λ A B → Hom B A 
_○ᵖ {Ob = Ob} C = record { id    = id
                         ; _○_   = λ f g   → g ○ f
                         ; lid   = λ f     → rid f
                         ; rid   = λ f     → lid f 
                         ; assoc = λ f g h → λ i → (assoc h g f) (~ i) }
    where open Category C 

-- TODO : refactor 
-- SET : Category {ℓ} λ A B → A → B
-- SET = record { id    = λ     x → x
--              ; _○_   = λ f g x → g (f x)
--              ; lid   = λ f     → refl
--              ; rid   = λ f     → refl 
--              ; assoc = λ f g h → refl }

-- DISCRETE : (A : Set ℓ) → Category {Ob = A} _≡_
-- DISCRETE A = record { id = refl 
--                     ; _○_ = λ p q → trans p q
--                     ; lid = λ p → {!!}
--                     ; rid = λ p → {!!}
--                     ; assoc = λ f g h → {!!} }
