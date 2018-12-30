{-# OPTIONS --cubical #-}

module Infinity.Category._Functor where

-- open import Infinity.Core 
open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Category.Cat

-- Canonical Functor definition
record Functor {Ob-A : Set ℓ} {Hom-A : Ob-A → Ob-A → Set ℓ} (Cat-A : Category Hom-A)
               {Ob-B : Set ℓ} {Hom-B : Ob-B → Ob-B → Set ℓ} (Cat-B : Category Hom-B)
               (Ob-F : Ob-A → Ob-B) : Set (ℓ-succ ℓ) where
  private module A = Category Cat-A
  private module B = Category Cat-B
  field 
    fmap          : ∀ {A B   : Ob-A} (_ : Hom-A A B)                 → Hom-B (Ob-F A) (Ob-F B)
    .{{presId}}   : ∀ {A     : Ob-A}                                 → fmap (A.id {A}) ≡ B.id {Ob-F A}
    .{{presComp}} : ∀ {A B C : Ob-A} (f : Hom-A A B) (g : Hom-A B C) → fmap (f A.◯ g)  ≡ (fmap f) B.◯ (fmap g)

-- Identity Functor 
idᶠ : ∀ {Ob : Set ℓ} {Hom : Ob → Ob → Set ℓ} {C : Category Hom} → Functor {ℓ} C C λ X → X
idᶠ {_} {Ob} {Hom} {C} = record { -- map      = λ x → Category.id C {x}
                                  fmap     = λ {A B} → idFun (Hom A B)
                                ; presId   = λ _   → id
                                ; presComp = λ _ _ → refl }
  where open Category C

-- Internal agda error 
-- module _ {Obj-A : Set ℓ} {Arr-A : Obj-A -> Obj-A -> Set ℓ} {Cat-A : Category Arr-A}
--          {Obj-B : Set ℓ} {Arr-B : Obj-B -> Obj-B -> Set ℓ} {Cat-B : Category Arr-B}
--          {Obj-C : Set ℓ} {Arr-C : Obj-C -> Obj-C -> Set ℓ} {Cat-C : Category Arr-C}
--          {Obj-F : Obj-A -> Obj-B} {Obj-G : Obj-B -> Obj-C} where
--   private
--     module R = Category Cat-A
--     module S = Category Cat-B
--     module T = Category Cat-C
    
--     _○ᶠ_ : Functor Cat-A Cat-B Obj-F
--          → Functor Cat-B Cat-C Obj-G
--          → Functor Cat-A Cat-C (λ x → Obj-G (Obj-F x))
--     (F ○ᶠ G) = record { map = ?
--                       ; fmap = λ x → G.fmap (F.fmap x)
--                       ; presId = λ A → trans (cong G.fmap (F.presId A)) (G.presId _)
--                       } where module F = Functor F 
--                               module G = Functor G
--     infixr 20 _○ᶠ_
    
-- Composition of Functors 
module _ {Obj-A : Set} {Arr-A : Obj-A → Obj-A → Set} {Cat-A : Category Arr-A}
         {Obj-B : Set} {Arr-B : Obj-B → Obj-B → Set} {Cat-B : Category Arr-B}
         {Obj-C : Set} {Arr-C : Obj-C → Obj-C → Set} {Cat-C : Category Arr-C}
         {Obj-F : Obj-A → Obj-B} {Obj-G : Obj-B → Obj-C}
  where
  private
    module R = Category Cat-A
    module S = Category Cat-B
    module T = Category Cat-C

  _○ᶠ_ : Functor Cat-A Cat-B Obj-F
       → Functor Cat-B Cat-C Obj-G
       → Functor Cat-A Cat-C (λ x → Obj-G (Obj-F x))
  Functor.fmap (F ○ᶠ G) = λ x → G.fmap (F.fmap x)
    where module F = Functor F 
          module G = Functor G 
  Functor.presId (F ○ᶠ G) = λ A → trans (cong G.fmap (F.presId A)) (G.presId _)
    where module F = Functor F
          module G = Functor G
  Functor.presComp (F ○ᶠ G) f g = λ f g → trans (cong G.fmap (F.presComp f g)) (G.presComp _ _)
    where module F = Functor F
          module G = Functor G
  infixr 20 _○ᶠ_
