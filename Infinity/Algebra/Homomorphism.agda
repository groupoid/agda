{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Homomorphism where 

open import Infinity.Proto
open import Infinity.Algebra.Group

record Homᴳ-Skeleton {eᴳ : Set ℓ₁} {eᴴ : Set ℓ₂} (Sᴳ : Group-Skeleton eᴳ) (Sᴴ : Group-Skeleton eᴴ) : Set (ℓ₁ ⊔ ℓ₂) where 
  constructor hom-skeleton
  private 
    module G = Group-Skeleton Sᴳ
    module H = Group-Skeleton Sᴴ
  field 
    p : eᴳ → eᴴ 
    preserves-composition : ∀ a₁ a₂ → p (a₁ G.· a₂) ≡ (p a₁) H.· (p a₂)
    
  -- abstract 
  --   preserves-id : p G.e ≡ H.e 
  --   preserves-id = {!!}
  --     -- H.←\ (f G.e) $ (f G.e) H.· (f G.e) ≡⟨ sym $ preserves-composition G.e G.e ⟩
  --     -- f (G.e G· G.e) ≡⟨ f (G.⊤⃐ G.e) ⟩
  --     -- f G.e ≡⟨ sym $ H.⊤⃑ (f G.e) ⟩ 
  --     -- (f G.e) H.· H.e ∎
    
  --   preserves-⁻¹ : ∀ g → p (g G.⁻¹) ≡ (p g) H.⁻¹
  --   preserves-⁻¹ g = {!!}
    
  --   preserves-difference : ∀ g h → p (g G.-ᴳ h) ≡ (p g) H.-ᴳ (p h)
  --   preserves-difference g h = {!!} 
    

record Homᴳ (G : Group ℓ₁) (H : Group ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where 
  constructor homᴳ
  private 
    module G = Group G 
    module H = Group H 
    _·ᴳ_ = G._·_
    _·ᴴ_ = H._·_
  field 
    p : G.E → H.E 
    preserves-composition : ∀ g₁ g₂ → p (g₁ ·ᴳ g₂) ≡ (p g₁) ·ᴴ (p g₂) 
  open Homᴳ-Skeleton {Sᴳ = G.Skeleton} {Sᴴ = H.Skeleton} 
    record {p = p ; preserves-composition = preserves-composition } hiding (p ; preserves-composition) public

infixr 0 _→ᴳ_ 
_→ᴳ_ = Homᴳ 
