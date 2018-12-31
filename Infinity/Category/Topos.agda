{-# OPTIONS --cubical #-}

module Infinity.Category.Topos where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Category.Cat 
open import Infinity.Category.Functor
open import Infinity.HIT.Pullback

Presheaf : ∀ {Ob : Set} {Hom : Ob → Ob → Set} (C : Category Hom) → Set
Presheaf C = Functor (C ᵒᵖ) SET

-- TODO : Hom a c ≠ Ob → Ob
has-pullbacks : ∀ {Ob : Set} {Hom : Ob → Ob → Set} → Set 
has-pullbacks {Ob = Ob} {Hom = Hom} = {a b c : Ob} (f : Hom a c) (g : Hom b c) → pullback {A = Ob} {B = Ob} {C = Ob} f g 
