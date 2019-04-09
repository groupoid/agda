{-# OPTIONS --cubical #-}

module Infinity.Algebra.Group.Subgroup where 

open import Infinity.Proto hiding (_∘_)
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Algebra.Base
open import Infinity.HIT.Trunc
open import Infinity.HIT.Subtype
open import Infinity.HIT.NType

record SubgroupProp ℓ₂ (G : Group ℓ₁) : Set (ℓ₁ ⊔ (ℓ-succ ℓ₂)) where 
  private 
    module G = Group G 
  field 
    prop  :            G.E                      → Set ℓ₂
    e     :                                       prop G.e
    _-_   : ∀ {g₁ g₂ : G.E} → prop g₁ → prop g₂ → prop (g₁ G.-ᴳ g₂)
    level : ∀ {g     : G.E}                     → isProp (prop g)
  abstract 
    _⁻¹ : ∀ {g} → prop g → prop (g G.⁻¹)
    _⁻¹ pg = subst prop (G.⊤⃐ _) (e - pg)
    
    _·_ : ∀ {g₁ g₂} → prop g₁ → prop g₂ → prop (g₁ G.· g₂)
    _·_ {g₁} {g₂} pg₁ pg₂ = subst prop (cong (g₁ G.·_) (g₂ G.⁻¹⁻¹)) (pg₁ - (pg₂ ⁻¹))
    
  subE-prop : SubtypeProp ℓ₂ G.E
  subE-prop = prop , λ _ → level 
  
  SubE = Subtype subE-prop

is-normal : ∀ {G : Group ℓ₁} → SubgroupProp ℓ₂ G → Set (ℓ₁ ⊔ ℓ₂)
is-normal {G = G} P = ∀ g₁ {g₂} → P.prop g₂ → P.prop (Group.conj G g₁ g₂)
  where module P = SubgroupProp P
  
NormalSubgroupProp : ∀ (G : Group ℓ₁) ℓ₂ → Set (ℓ₁ ⊔ (ℓ-succ ℓ₂))
NormalSubgroupProp G ℓ₂ = Σ (SubgroupProp ℓ₂ G) is-normal

module _ {G : Group ℓ₁} (P : SubgroupProp ℓ₂ G) where
  private
    module G = Group G
    module P = SubgroupProp P

  subgroup-skeleton : Group-Skeleton P.SubE
  subgroup-skeleton = record {M} where
    module M where
      e : P.SubE
      e = G.e , P.e

      _⁻¹ : P.SubE → P.SubE
      _⁻¹ (g , p) = g G.⁻¹ , p P.⁻¹

      _·_ : P.SubE → P.SubE → P.SubE
      (g₁ , p₁) · (g₂ , p₂) = g₁ G.· g₂ , p₁ P.· p₂
      
      abstract
        ⊤⃐ : ∀ g → e · g ≡ g 
        ⊤⃐ (g , _) = <:≡:>→≡ P.subE-prop (G.⊤⃐ g)
        
        assoc : ∀ g₁ g₂ g₃ → (g₁ · g₂) · g₃ ≡ g₁ · (g₂ · g₃) 
        assoc (g₁ , _) (g₂ , _) (g₃ , _) = prop-≡ P.subE-prop (G.assoc g₁ g₂ g₃)

  Subgroup : Group (ℓ₁ ⊔ ℓ₂)
  Subgroup = group _ subgroup-skeleton
    -- where abstract instance SubE-level = Subtype-level P.subE-prop

module Subgroup {G : Group ℓ₁} (P : SubgroupProp ℓ₂ G) where 
  private 
    module P = SubgroupProp P
    module G = Group G 
    
  g = Subgroup P 
  open Group g public 
