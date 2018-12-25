{-# OPTIONS --cubical --safe #-}
module Infinity.Univ where

open import Agda.Builtin.Sigma renaming ( snd to π⃑; fst to π⃐)
open import Infinity.Proto
open import Infinity.Path
open import Infinity.Equiv
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

open isEquiv public

fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ ⊔ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] (f x ≡ y)
  where open import Infinity.Sigma using (Σ-syntax)

equivIsEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = π⃑ e


equivCtr : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .π⃑ .equiv-proof y .π⃐

equivCtrPath : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B)
               → (v : fiber (equivFun e) y) → Path _ (equivCtr e y) v
equivCtrPath e y = e .π⃑ .equiv-proof y .π⃑

Glue : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I} → (Te : Partial φ (Σ[ T ∈ Set ℓ' ] T ≃ A)) → Set ℓ'
Glue A Te = primGlue A (λ x → Te x .π⃐) (λ x → Te x .π⃑)

idIsEquiv : ∀ {ℓ} → (A : Set ℓ) → isEquiv (λ (a : A) → a)
equiv-proof (idIsEquiv A) y = (y , refl) , λ z i → z .π⃑ (~ i) , λ j → z .π⃑ (~ i ∨ j)

idEquiv : ∀ {ℓ} → (A : Set ℓ) → A ≃ A
idEquiv A = (λ a → a) , idIsEquiv A

ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua {_} {A} {B} e i = Glue B (λ { (i = i0) → (A , e) ; (i = i1) → (B , idEquiv B) })

isoToPath : ∀ {ℓ} {A B : Set ℓ} (f : A → B)(g : B → A)(s : (y : B) → f (g y) ≡ y)(t : (x : A) → g (f x) ≡ x) → A ≡ B
isoToPath f g s t = ua (isoToEquiv f g s t)

unglueIsEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I) (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) →
                isEquiv {A = Glue A f} (unglue {φ = φ})
equiv-proof (unglueIsEquiv A φ f) = λ (b : A) →
  let u : I → Partial φ A
      u i = λ{ (φ = i1) → equivCtr (f 1=1 .π⃑) b .π⃑ (~ i) }
      ctr : fiber (unglue {φ = φ}) b
      ctr = ( glue (λ { (φ = i1) → equivCtr (f 1=1 .π⃑) b .π⃐ }) (hcomp u b)
            , λ j → hfill u (inc b) (~ j))
  in ( ctr
     , λ (v : fiber (unglue {φ = φ}) b) i →
         let u' : I → Partial (φ ∨ ~ i ∨ i) A
             u' j = λ { (φ = i1) → equivCtrPath (f 1=1 .π⃑) b v i .π⃑ (~ j)
                      ; (i = i0) → hfill u (inc b) j
                      ; (i = i1) → v .π⃑ (~ j) }
         in ( glue (λ { (φ = i1) → equivCtrPath (f 1=1 .π⃑) b v i .π⃐ }) (hcomp u' b)
            , λ j → hfill u' (inc b) (~ j)))

unglueEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I) (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) → (Glue A f) ≃ A
unglueEquiv A φ f = ( unglue {φ = φ} , unglueIsEquiv A φ f )

EquivContr : ∀ {ℓ} (A : Set ℓ) → isContr (Σ[ T ∈ Set ℓ ] T ≃ A)
EquivContr {ℓ} A =
  ( ( A , idEquiv A)
  , λ w i → let f : PartialP (~ i ∨ i) (λ x → Σ[ T ∈ Set ℓ ] T ≃ A)
                f = λ { (i = i0) → A , idEquiv A ; (i = i1) → w }
            in ( Glue A f , unglueEquiv _ _ f) )
