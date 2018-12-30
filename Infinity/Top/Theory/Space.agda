{-# OPTIONS --cubical --safe #-}

module Infinity.Top.Theory.Space where 

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Path
open import Infinity.Top.Space 
open import Infinity.Top.Predicate
open import Infinity.Category.Cat 

OpenSetCat : ∀ {S : Space} → Category {ℓ} {Σ _ (Space.Open S)} λ U V → π⃐ U ⊆ π⃐ V
OpenSetCat = record { id    = λ _ x → x
                    ; _○_   = λ f g x y → f x (g x y) 
                    ; lid   = refl 
                    ; rid   = refl 
                    ; assoc = refl }
                  

