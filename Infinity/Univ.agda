{-# OPTIONS --cubical --safe #-}

module Infinity.Univ where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Equiv
open import Infinity.Retract
open import Infinity.Fibration
open import Infinity.HIT.NType
open import Infinity.Sigma

open import Agda.Builtin.Cubical.Glue public
     using ( isEquiv
           ; _≃_
           ; equivFun
           ; equivProof
           ; primGlue
           ; primFaceForall
           )
     renaming ( prim^glue   to glue
              ; prim^unglue to unglue
              ; pathToEquiv to lineToEquiv
              )

Glue : (A : Set ℓ₁) {φ : I} → (e : Partial φ (Σ[ T ∈ Set ℓ₂ ] T ≃ A)) → Set ℓ₂
Glue A e = primGlue A (λ x → e x .π⃐) (λ x → e x .π⃑)

idIsEquiv : (A : Set ℓ) → isEquiv (λ (a : A) → a)
equiv-proof (idIsEquiv A) y = (y , refl) , λ z i → z .π⃑ (~ i) , λ j → z .π⃑ (~ i ∨ j)

idEquiv : (A : Set ℓ) → A ≃ A
idEquiv A = (λ a → a) , idIsEquiv A

module _ {A B : Set ℓ} where 
    ua : A ≃ B → A ≡ B
    ua e i = Glue B (λ { (i = i0) → (A , e) ; (i = i1) → (B , idEquiv B) })

    uaβ : (e : A ≃ B) (x : A) → coe (ua e) x ≡ e .π⃐ x 
    uaβ = coe≡ ⦂ π⃐

coe≃ : ∀ {A B : Set ℓ} → (A ≃ B) → (A → B)
coe≃ = Infinity.Path.coe ∘ ua

≃→≡ : ∀ {A B : Set ℓ} (f : A → B) (g : B → A) (s : (y : B) → f (g y) ≡ y) (t : (x : A) → g (f x) ≡ x) → A ≡ B
≃→≡ = ua ⦂⦂ ≈→≃

≈→≡ : ∀ {A B : Set ℓ} (f : A → B) (g : B → A) (s : section f g) (t : retract f g) → A ≡ B 
≈→≡ {_} {A} {B} f g s t = λ i → Glue B (λ { (i = i0) → _ , ≈→≃ f g s t 
                                          ; (i = i1) → _ , _ , idIsEquiv B })

unglueIsEquiv : (A : Set ℓ) (φ : I) (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) → isEquiv {A = Glue A f} (unglue {φ = φ})
equiv-proof (unglueIsEquiv A φ f) = λ (b : A) →
  let u : I → Partial φ A
      u i = λ{ (φ = i1) → equivCtr (f 1=1 .π⃑) b .π⃑ (~ i) }
      ctr : fiber (unglue {φ = φ}) b
      ctr = ( glue (λ { (φ = i1) → equivCtr (f 1=1 .π⃑) b .π⃐ }) (hcomp u b)
            , λ j → hfill u (inc b) (~ j))
  in (ctr , λ (v : fiber (unglue {φ = φ}) b) i →
              let u' : I → Partial (φ ∨ ~ i ∨ i) A
                  u' j = λ { (φ = i1) → equivCtrPath (f 1=1 .π⃑) b v i .π⃑ (~ j)
                           ; (i = i0) → hfill u (inc b) j
                           ; (i = i1) → v .π⃑ (~ j) }
              in (glue (λ { (φ = i1) → equivCtrPath (f 1=1 .π⃑) b v i .π⃐ }) (hcomp u' b) , λ j → hfill u' (inc b) (~ j)))

unglueEquiv : (A : Set ℓ) (φ : I) (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) → (Glue A f) ≃ A
unglueEquiv _ φ _ .π⃐ = unglue {φ = φ}
unglueEquiv A φ f .π⃑ = unglueIsEquiv A φ f

EquivContr : (A : Set ℓ) → isContr (Σ[ T ∈ Set ℓ ] T ≃ A)
EquivContr {ℓ} A =
  ( ( A , idEquiv A ) , idEquiv≡ )
 where
  idEquiv≡ : (y : Σ[ T ∈ Set ℓ ] T ≃ A) → (A , idEquiv A) ≡ y
  idEquiv≡ w = \ { i .π⃐                   → Glue A (f i)
                 ; i .π⃑ .π⃐              → unglueEquiv _ _ (f i) .π⃐
                 ; i .π⃑ .π⃑ .equiv-proof → unglueEquiv _ _ (f i) .π⃑ .equiv-proof
                 }
    where
      f : ∀ i → PartialP (~ i ∨ i) (λ x → Σ[ T ∈ Set ℓ ] T ≃ A)
      f i = λ { (i = i0) → A , idEquiv A ; (i = i1) → w }