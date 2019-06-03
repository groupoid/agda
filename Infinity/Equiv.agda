{-# OPTIONS --cubical --safe #-}

module Infinity.Equiv where

open import Infinity.Path
open import Infinity.Sigma
open import Infinity.Retract
open import Infinity.HIT.NType
-- open import Infinity.HIT.Subtype

open import Agda.Builtin.Cubical.Glue using (isEquiv ; _≃_ ; equivFun) public

open isEquiv using (equiv-proof) public

module _ {A : Set ℓ₁} {B : Set ℓ₂} where 

  isPropIsEquiv' : (f : A → B) → isProp (isEquiv f)
  equiv-proof (isPropIsEquiv' _ u₁ u₂ i) y = isPropIsContr (u₁ .equiv-proof y) (u₂ .equiv-proof y) i

  isPropIsEquiv : (f : A → B) → isProp (isEquiv f)
  equiv-proof (isPropIsEquiv f p₁ q₁ i) y =
    let p₂ = p₁ .equiv-proof y .π⃑
        q₂ = q₁ .equiv-proof y .π⃑
    in p₂ (q₁ .equiv-proof y .π⃐) i , λ w j → hcomp (λ k → λ { (i = i0) → p₂ w j
                                                            ; (i = i1) → q₂ w (j ∨ ~ k)
                                                            ; (j = i0) → p₂ (q₂ w (~ k)) i
                                                            ; (j = i1) → w }) (p₂ w (i ∨ j))

record ≈-Skeleton {A : Set ℓ₁} {B : Set ℓ₂} : Set (ℓ₁ ⊔ ℓ₂) where 
  constructor iso
  field 
    f : A → B
    g : B → A 
    s : section f g 
    t : retract f g 
    
module _ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (g : B → A) (s : section f g) (t : retract f g) where
  private
    module _ (y : B) (a₁ a₂ : A) (p₁ : f a₁ ≡ y) (p₂ : f a₂ ≡ y) where

      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t a₁ k; (i = i0) → g y }) (inc (g (p₁ (~ i))))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t a₂ k; (i = i0) → g y }) (inc (g (p₂ (~ i))))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1; (i = i0) → fill0 k i1 }) (inc (g y))

      p : a₁ ≡ a₂
      p i = fill2 i i1

      sq₁ : I → I → A
      sq₁ i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                               ; (i = i0) → fill0 j (~ k)
                               ; (j = i1) → t (fill2 i i1) (~ k)
                               ; (j = i0) → g y }) (fill2 i j)

      sq₂ : I → I → B
      sq₂ i j = hcomp (λ k → λ { (i = i1) → s (p₂ (~ j)) k
                               ; (i = i0) → s (p₁ (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k }) (f (sq₁ i j))

      lemIso : (a₁ , p₁) ≡ (a₂ , p₂)
      lemIso = λ i → p i , λ j → sq₂ i (~ j)

  ≈→IsEquiv : isEquiv f
  ≈→IsEquiv .equiv-proof y .π⃐ .π⃐ = g y
  ≈→IsEquiv .equiv-proof y .π⃐ .π⃑ = s y
  ≈→IsEquiv .equiv-proof y .π⃑ z = lemIso y (g y) (π⃐ z) (s y) (π⃑ z)

  ≈→≃ : A ≃ B
  ≈→≃ = _ , ≈→IsEquiv

module _ {A : Set ℓ₁} {B : A → Set ℓ₂} where

  propPi : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
  propPi h f g i x = h x (f x) (g x) i

  isProp→PathP : ((x : A) → isProp (B x)) → {a₁ a₂ : A} (p : a₁ ≡ a₂) (b₁ : B a₁) (b₂ : B a₂) → PathP (λ i → B (p i)) b₁ b₂
  isProp→PathP P p b₁ b₂ i = P (p i) (transp (λ j → B (p (i ∧ j))) (~ i) b₁) (transp (λ j → B (p (i ∨ ~ j))) i b₂) i

equivEq : ∀ {A : Set ℓ₁} {B : Set ℓ₂} (e f : A ≃ B) → (h : e .π⃐ ≡ f .π⃐) → e ≡ f
equivEq e f h = λ i → (h i) , isProp→PathP isPropIsEquiv h (e .π⃑) (f .π⃑) i

module _ {A : Set ℓ₁} {B : Set ℓ₂} (w : A ≃ B) where
  inv≃ : B → A
  inv≃ y = w .π⃑ .equiv-proof y .π⃐ .π⃐

  sec≃ : (x : A) → inv≃ (π⃐ w x) ≡ x
  sec≃ x = λ i → w .π⃑ .equiv-proof (w .π⃐ x) .π⃑ (x , λ j → π⃐ w x) i .π⃐

  ret≃ : (y : B) → π⃐ w (inv≃ y) ≡ y
  ret≃ y = w .π⃑ .equiv-proof y .π⃐ .π⃑ 
  
≃⁻¹ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → A ≃ B → B ≃ A
≃⁻¹ f = ≈→≃ (inv≃ f) (π⃐ f) (sec≃ f) (ret≃ f)

compEquiv : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → A ≃ B → B ≃ C → A ≃ C
compEquiv f g = ≈→≃ (λ x → g .π⃐ (f .π⃐ x))
                    (λ x → inv≃ f (inv≃ g x))
                    (λ y → compPath (cong (π⃐    g) (ret≃ f (inv≃ g y))) (ret≃ g y))
                    (λ y → compPath (cong (inv≃ f) (sec≃ g (  f .π⃐ y))) (sec≃ f y))
