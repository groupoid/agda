{-# OPTIONS --cubical #-}

module Infinity.Category.Profunctor where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Category.Base 

record Profunctor (p : Set ℓ → Set ℓ → Set ℓ) : Set (ℓ-succ ℓ) where
  field 
    dimap : {a b c d : Set ℓ} → (a → b) → (c → d) → p b c → p a d 
    
  lmap : ∀ {a b c} → (a → b) → p b c → p a c 
  lmap f = dimap f (λ x → x)
    
  rmap : ∀ {a b c} → (b → c) → p a b → p a c
  rmap f = dimap (λ x → x) f 
  
  field 
    {{.profunctor-id}} : {a c : Set ℓ} → ∀ x → dimap (idFun a) (idFun c) x ≡ x
    {{.profunctor-∘}}  : {a b c d e : Set ℓ} → {f : b → c} {g : a → b} {h : d → e} {i : c → d} 
                       → ∀ x → dimap (f ∘ g) (h ∘ i) x ≡ (dimap g h ∘ dimap f i) x
                       
record Review (_ b : Set ℓ) : Set ℓ where
  constructor review 
  field get : b

record Forget (r a _ : Set ℓ) : Set ℓ where
  constructor forget
  field f : a → r

