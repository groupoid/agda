{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Infinity.Algebra.Group.Base where 

open import Infinity.Proto hiding (_∘_)
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Inductive.One
open import Infinity.Inductive.Z
open import Infinity.Inductive.Empty
open import Infinity.HIT.Subtype

record Group-Skeleton (E : Set ℓ) : Set ℓ where 
  constructor group
  field 
    id        :         E 
    _⁻¹       : E     → E
    _∘_       : E → E → E 
    -- {{⊤⃐}}     : ∀ A     → id ∘ A      ≡ A 
    -- {{assoc}} : ∀ A B C → (A ∘ B) ∘ C ≡ A ∘ (B ∘ C)
    -- {{_⁻¹⃐}}   : ∀ A     → (A  ⁻¹) ∘ A ≡ id

  private 
    infix 80 _∘_

  abstract
    _⁻¹⃑ : ∀ G → G ∘ G ⁻¹ ≡ id 
    _⁻¹⃑ = {!!}
    
    _⁻¹⁻¹ : (g : E) → (g ⁻¹) ⁻¹ ≡ g 
    g ⁻¹⁻¹ = {!!}

  -- exp : E → ℤ → E 
  -- exp e (pos 0) = id 
  -- exp e (pos 1) = e
  -- exp e (pos 2) = e ∘ (exp e (pos 1))
  -- exp e (negsucc 0) = e ⁻¹
  -- exp e (negsucc (S n)) = e ⁻¹ ∘ (exp e (negsucc n))
  
  _-ᴳ_ : E → E → E 
  g -ᴳ h = g ∘ h ⁻¹
  
  conj : E → E → E 
  conj g h = (g ∘ h) ∘ g ⁻¹
  
record Group ℓ : Set (ℓ-succ ℓ) where 
  constructor group 
  field 
    E : Set ℓ 
    -- {{.E-level}} : has-level 0 E 
    Skeleton : Group-Skeleton E 
  open Group-Skeleton Skeleton public 
      
Group₀ : Set₁ 
Group₀ = Group ℓ-zero

is-trivial : Group ℓ → Set ℓ 
is-trivial G = ∀ g → g ≡ Group.id G

module _ {A : Set ℓ₁} {ℓ₂} (r : R A ℓ₂) where 
  is-refl : Set (ℓ₁ ⊔ ℓ₂)
  is-refl = ∀ a → r a a 
  
  is-sym : Set (ℓ₁ ⊔ ℓ₂)
  is-sym = ∀ {a b} → r a b → r b a 
  
  is-trans : Set (ℓ₁ ⊔ ℓ₂)
  is-trans = ∀ {a b c} → r a b → r b c → r a c 
  
0ᴳ-Skeleton : Group-Skeleton ⊤
0ᴳ-Skeleton = record {G} where 
  module G where 
    id  =         unit
    _⁻¹ = λ _   → unit
    _∘_ = λ _ _ → unit

0ᴳ : Group ℓ-zero 
0ᴳ = group _ 0ᴳ-Skeleton

_↑ᴳ : Group ℓ₁ → Group (ℓ₁ ⊔ ℓ₂)
G ↑ᴳ = {!!} -- group (↑ E) (↑ᴳ-Skeleton group-struct) where open Group G 
