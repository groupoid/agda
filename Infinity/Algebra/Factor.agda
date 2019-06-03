{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Factor where 

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Equiv
-- open import Infinity.HIT.Subtype
open import Infinity.Algebra.Base 
open import Infinity.Algebra.Homomorphism
open import Infinity.Algebra.Group
open import Infinity.Algebra.Subgroup

data Quotient {A : Set ℓ} (R : A → A → Set ℓ) : Set ℓ where 
  inj : A → Quotient {A = A} _
  eq  : (a b : A) {{_ : R a b}} → inj a ≡ inj b 
  
-- /₀ : ∀ {X : Set ℓ₁} (R : R X ℓ₂) → Set (ℓ₁ ⊔ (ℓ-succ ℓ₂))
-- /₀ {ℓ₂ = ℓ₂} {X = X} R = Σ[ A ∈ SubtypeProp ℓ₂ X ] IsEquivClass X R A

-- _/_ : (A : Set ℓ) (R : A → A → Set ℓ) → Set (ℓ-succ ℓ)
-- A / R = /₀ {X = A} R

-- infix 0 _/ᴳ_
-- _/ᴳ_ : (G : Group ℓ) (R : G →ᴳ G → Group ℓ) → Set (ℓ-succ ℓ)
-- -- _/ᴳ_ : (G : Group ℓ) (R : (Group.E G) → (Group.E G) → Group ℓ) → Group (ℓ-succ ℓ)
-- -- G /ᴳ R = /₀ {X = Group.E G} R
-- _/ᴳ_ {ℓ = ℓ} G R = Σ[ A ∈ SubtypeProp ℓ (Group.E G) ] IsEquivClass (Group.E G) {!!} A 

-- -- Group quotients 
module _ {G : Group ℓ₁} (P : NormalSubgroupProp G ℓ₂) where
  private
    module G = Group G
    module P = NormalSubgroupProp P
    infix 80 _·_
    _·_ = G.comp

  quot-group-rel : R G.E ℓ₂
  quot-group-rel g₁ g₂ = P.prop (G.diff g₁ g₂)

  quot-group-struct : GroupStructure (SetQuot quot-group-rel)
  quot-group-struct = record {M} where
    module M where
      ident : SetQuot quot-group-rel
      ident = q[ G.ident ]

      abstract
        inv-rel : ∀ {g₁ g₂ : G.El} (pg₁g₂⁻¹ : P.prop (G.diff g₁ g₂))
          → q[ G.inv g₁ ] == q[ G.inv g₂ ] :> SetQuot quot-group-rel
        inv-rel {g₁} {g₂} pg₁g₂⁻¹ = ! $ quot-rel $
          transport! (λ g → P.prop (G.inv g₂ ⊙ g))
            (G.inv-inv g₁) $ P.comm g₁ (G.inv g₂) pg₁g₂⁻¹

      inv : SetQuot quot-group-rel → SetQuot quot-group-rel
      inv = SetQuot-rec (λ g → q[ G.inv g ]) inv-rel

      abstract
        comp-rel-r : ∀ g₁ {g₂ g₂' : G.El} (pg₂g₂'⁻¹ : P.prop (G.diff g₂ g₂'))
          → q[ g₁ ⊙ g₂ ] == q[ g₁ ⊙ g₂' ] :> SetQuot quot-group-rel
        comp-rel-r g₁ {g₂} {g₂'} pg₂g₂'⁻¹ = quot-rel $ transport P.prop
          ( ap (_⊙ G.inv g₁) (! $ G.assoc g₁ g₂ (G.inv g₂'))
          ∙ G.assoc (g₁ ⊙ g₂) (G.inv g₂') (G.inv g₁)
          ∙ ap ((g₁ ⊙ g₂) ⊙_) (! $ G.inv-comp g₁ g₂'))
          (P.conj g₁ pg₂g₂'⁻¹)

      comp' : G.El → SetQuot quot-group-rel → SetQuot quot-group-rel
      comp' g₁ = SetQuot-rec (λ g₂ → q[ g₁ ⊙ g₂ ]) (comp-rel-r g₁)

      abstract
        comp-rel-l : ∀ {g₁ g₁' : G.El} (pg₁g₁'⁻¹ : P.prop (G.diff g₁ g₁')) g₂
          → q[ g₁ ⊙ g₂ ] == q[ g₁' ⊙ g₂ ] :> SetQuot quot-group-rel
        comp-rel-l {g₁} {g₁'} pg₁g₁'⁻¹ g₂ = quot-rel $ transport! P.prop
            ( ap ((g₁ ⊙ g₂) ⊙_) (G.inv-comp g₁' g₂)
            ∙ ! (G.assoc (g₁ ⊙ g₂) (G.inv g₂) (G.inv g₁') )
            ∙ ap (_⊙ G.inv g₁')
              ( G.assoc g₁ g₂ (G.inv g₂)
              ∙ ap (g₁ ⊙_) (G.inv-r g₂)
              ∙ G.unit-r g₁))
            pg₁g₁'⁻¹

        comp'-rel : ∀ {g₁ g₁' : G.El} (pg₁g₁'⁻¹ : P.prop (G.diff g₁ g₁'))
          → comp' g₁ == comp' g₁'
        comp'-rel pg₁g₁'⁻¹ = λ= $ SetQuot-elim
          (comp-rel-l pg₁g₁'⁻¹)
          (λ _ → prop-has-all-paths-↓)

      comp : SetQuot quot-group-rel → SetQuot quot-group-rel → SetQuot quot-group-rel
      comp = SetQuot-rec comp' comp'-rel

      abstract
        unit-l : ∀ g → comp ident g == g
        unit-l = SetQuot-elim
          (ap q[_] ∘ G.unit-l)
          (λ _ → prop-has-all-paths-↓)

        assoc : ∀ g₁ g₂ g₃ → comp (comp g₁ g₂) g₃ == comp g₁ (comp g₂ g₃)
        assoc = SetQuot-elim
          (λ g₁ → SetQuot-elim
            (λ g₂ → SetQuot-elim
              (λ g₃ → ap q[_] $ G.assoc g₁ g₂ g₃)
              (λ _ → prop-has-all-paths-↓))
            (λ _ → prop-has-all-paths-↓))
          (λ _ → prop-has-all-paths-↓)

        inv-l : ∀ g → comp (inv g) g == ident
        inv-l = SetQuot-elim
          (ap q[_] ∘ G.inv-l)
          (λ _ → prop-has-all-paths-↓)

  QuotGroup : Group (lmax i j)
  QuotGroup = group _ quot-group-struct
