{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Group.Base where 

open import Infinity.Proto hiding (_∘_)
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Reason
open import Infinity.Inductive.One
open import Infinity.Inductive.Two
open import Infinity.Inductive.Z
open import Infinity.Inductive.Empty
-- open import Infinity.HIT.Subtype

record Group-Skeleton (E : Set ℓ) : Set ℓ where 
  constructor group-skeleton
  field 
    e     :         E 
    _⁻¹   : E     → E
    _·_   : E → E → E 
    ⊤⃐     : ∀ g       →  e · g      ≡ g
    assoc : ∀ A B C   → (A · B) · C ≡ A · (B · C)
    _⁻¹⃐   : ∀ A       → (A  ⁻¹) · A ≡ e

  private 
    infix 90 _⁻¹
    infix 80 _·_

  abstract 
    _⁻¹⃑ : ∀ g → g · g ⁻¹ ≡ e
    g ⁻¹⃑ = 
        g · g ⁻¹                       ≡⟨ sym $ ⊤⃐ (g · g ⁻¹)                                                           ⟩ 
        e · (g · g ⁻¹)                 ≡⟨ sym $ (g ⁻¹) ⁻¹⃐                           |in (λ h → h · (g · g ⁻¹))         ⟩
      ((g ⁻¹) ⁻¹ · g ⁻¹) · (g · g ⁻¹)  ≡⟨       assoc ((g ⁻¹) ⁻¹) (g ⁻¹) (g · g ⁻¹)                                    ⟩
       (g ⁻¹) ⁻¹ · (g ⁻¹ · (g · g ⁻¹)) ≡⟨ sym $ assoc (g ⁻¹) g (g ⁻¹)               |in (λ h → (g ⁻¹) ⁻¹ · h)          ⟩
       (g ⁻¹) ⁻¹ · ((g ⁻¹ · g) · g ⁻¹) ≡⟨       g ⁻¹⃐                                |in (λ h → (g ⁻¹) ⁻¹ · (h · g ⁻¹)) ⟩
       (g ⁻¹) ⁻¹ · (e · g ⁻¹)          ≡⟨       ⊤⃐ (g ⁻¹)                            |in (λ h → (g ⁻¹) ⁻¹ · h)          ⟩
       (g ⁻¹) ⁻¹ ·  g ⁻¹               ≡⟨       (g ⁻¹) ⁻¹⃐                                                              ⟩
        e ∎
    
    ⊤⃑ : ∀ g → g · e ≡ g 
    ⊤⃑ g = 
       g · e          ≡⟨ sym $ g ⁻¹⃐             |in g ·_ ⟩
       g · (g ⁻¹ · g) ≡⟨ sym $ assoc g (g ⁻¹) g          ⟩
      (g · g ⁻¹) · g  ≡⟨       g ⁻¹⃑             |in _· g ⟩
       e · g          ≡⟨       ⊤⃐ g                       ⟩
       g ∎
       
    ⁻¹-uniq : (g h : E) → g · h ≡ e → g ⁻¹ ≡ h
    ⁻¹-uniq g h p = 
       g ⁻¹ ≡⟨ sym $ ⊤⃑ (g ⁻¹) ⟩
       g ⁻¹ · e ≡⟨ sym $ p |in g ⁻¹ ·_ ⟩
       g ⁻¹ · (g · h) ≡⟨ sym $ assoc (g ⁻¹) g h ⟩
      (g ⁻¹ · g) · h ≡⟨ g ⁻¹⃐ |in _· h ⟩
       e · h ≡⟨ ⊤⃐ h ⟩
       h ∎
       
    _⁻¹⁻¹ : ∀ g → (g ⁻¹) ⁻¹ ≡ g 
    g ⁻¹⁻¹ = ⁻¹-uniq (g ⁻¹) g (g ⁻¹⃐)

    -- _⁻¹⁻¹ : ∀ g → (g ⁻¹) ⁻¹ ≡ g 
    -- g ⁻¹⁻¹ = 
    --    g ≡⟨ sym $ ⊤⃑ g ⟩
    --    g · e ≡⟨ sym $ g ⁻¹⃐ |in (λ h → g · h) ⟩
    --    g · (g ⁻¹ · g) ≡⟨ sym $ assoc g (g ⁻¹) g ⟩
    --   (g · g ⁻¹) · g ≡⟨ (g ⁻¹) ⁻¹⃐ |in _· g ⟩
    --    e · g ≡⟨ ⊤⃐ g ⟩
    --    g ∎
    
    -- ←\ : (g : E) {h k : E} → g · h ≡ g · k → h ≡ k
    -- ←\ g {h} {k} p = 
    --   h ≡⟨ sym $ ⊤⃐ h ⟩
    --   e · h ≡⟨ sym (g ⁻¹⃐) · h ⟩
    --   (g ⁻¹ · g) · h ≡⟨ assoc (g ⁻¹) g h ⟩
    --   g ⁻¹ · (g · h) ≡⟨ g ⁻¹ · p ⟩
    --   g ⁻¹ · (g · k) ≡⟨ sym $ assoc (g ⁻¹) g k ⟩
    --   (g ⁻¹ · g) · k ≡⟨ g ⁻¹ · k ⟩
    --   e · k ≡⟨ ⊤⃐ k ⟩
    --   k ∎

    -- →\ : (g : E) {h k : E} → h · g ≡ k · g → h ≡ k
    -- →\ g {h} {k} p = {!!}

  _^_ : E → ℤ → E 
  e ^ (pos       0 ) = e
  e ^ (pos       1 ) = e
  e ^ (pos (succ n)) = e · (e ^ (pos n))
  e ^ (neg       0 ) = e ⁻¹
  e ^ (neg (succ n)) = (e ⁻¹) · (e ^ (neg n))
  
  _-ᴳ_ : E → E → E 
  g -ᴳ h = g · h ⁻¹
  
  conj : E → E → E 
  conj g h = (g · h) · g ⁻¹
  
record Group ℓ : Set (ℓ-succ ℓ) where 
  constructor group 
  field 
    E : Set ℓ 
    Skeleton : Group-Skeleton E 
  open Group-Skeleton Skeleton public 
      
Group₀ : Set₁ 
Group₀ = Group ℓ-zero

is-trivial : Group ℓ → Set ℓ 
is-trivial G = ∀ g → g ≡ Group.e G

𝟙-Skeleton : Group-Skeleton {ℓ} ⊤
𝟙-Skeleton = record {G} where 
  module G where 
    e     =           unit
    _⁻¹   = λ _     → unit
    _·_   = λ _ _   → unit
    ⊤⃐     = λ _     → refl
    assoc = λ _ _ _ → refl
    _⁻¹⃐   = λ _     → refl

𝟙ᴳ : Group ℓ-zero 
𝟙ᴳ = group _ 𝟙-Skeleton

-- 𝟙≡𝟙ᴳ = 𝟙 ≡ 𝟙ᴳ
-- 𝟙≡𝟙ᴳ = ?

-- 𝟚-Skeleton : Group-Skeleton 𝟚
-- 𝟚-Skeleton = record {G} where 
--   module G where 
--     e = 𝟘
--     _·_ = _∨_
--     _⁻¹ = ¬_
--     assoc = ? -- ∨-assoc 
--     τ⃐ = ? -- 𝟘←id
--     _⁻¹⃐ = ? -- 𝟘←¬

-- 𝟚ᴳ : Group ℓ-zero
-- 𝟚ᴳ = group _ 𝟚-Skeleton 

-- _↑ᴳ : Group ℓ₁ → Group (ℓ₁ ⊔ ℓ₂)
-- G ↑ᴳ = group (↑ E) (↑ᴳ-Skeleton group-struct) where open Group G 
