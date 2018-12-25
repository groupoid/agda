{-# OPTIONS --cubical --safe #-}
module Infinity.Univ where

open import Agda.Builtin.Sigma renaming ( snd to π⃑; fst to π⃐)
open import Infinity.Proto
open import Infinity.Path
open import Infinity.Sigma
open import Agda.Builtin.Cubical.Glue public
  using ( isEquiv       -- isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ')

        ; _≃_           -- ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')

        ; equivFun      -- ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B

        ; equivProof    -- ∀ {la lt} (T : Set la) (A : Set lt) → (w : T ≃ A) → (a : A)
                        -- → ∀ ψ → (Partial ψ (fiber (equivFun w) a)) → fiber (equivFun w) a

        ; primGlue      -- ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
                        -- → (T : Partial φ (Set ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
                        -- → Set ℓ'

        -- Needed for transp in Glue.
        ; primFaceForall -- (I → I) → I
        )
  renaming ( prim^glue   to glue         -- ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
                                         -- → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
                                         -- → PartialP φ T → A → primGlue A T e

           ; prim^unglue to unglue       -- ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
                                         -- → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
                                         -- → primGlue A T e → A

           ; pathToEquiv to lineToEquiv  -- {ℓ : I → Level} (P : (i : I) → Set (ℓ i)) → P i0 ≃ P i1
           )

open isEquiv public

fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ ⊔ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] (f x ≡ y)
  where open import Infinity.Sigma using (Σ-syntax)

equivIsEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = π⃑ e

equivCtr : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .π⃑ .equiv-proof y .π⃐

equivCtrPath : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e : A ≃ B) (y : B) →
  (v : fiber (equivFun e) y) → Path _ (equivCtr e y) v
equivCtrPath e y = e .π⃑ .equiv-proof y .π⃑


-- We uncurry Glue to make it a bit more pleasant to use
Glue : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Set ℓ' ] T ≃ A))
       → Set ℓ'
Glue A Te = primGlue A (λ x → Te x .π⃐) (λ x → Te x .π⃑)


-- The identity equivalence
idIsEquiv : ∀ {ℓ} → (A : Set ℓ) → isEquiv (λ (a : A) → a)
equiv-proof (idIsEquiv A) y = (y , refl) , λ z i → z .π⃑ (~ i) , λ j → z .π⃑ (~ i ∨ j)

idEquiv : ∀ {ℓ} → (A : Set ℓ) → A ≃ A
idEquiv A = (λ a → a) , idIsEquiv A

-- The ua constant
ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
ua {_} {A} {B} e i =
  Glue B (λ { (i = i0) → (A , e)
            ; (i = i1) → (B , idEquiv B) })

-- Proof of univalence using that unglue is an equivalence:

-- unglue is an equivalence
unglueIsEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I)
                (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) →
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

-- Any partial family of equivalences can be extended to a total one
-- from Glue [ φ ↦ (T,f) ] A to A
unglueEquiv : ∀ {ℓ} (A : Set ℓ) (φ : I)
              (f : PartialP φ (λ o → Σ[ T ∈ Set ℓ ] T ≃ A)) →
              (Glue A f) ≃ A
unglueEquiv A φ f = ( unglue {φ = φ} , unglueIsEquiv A φ f )


-- The following is a formulation of univalence proposed by Martín Escardó:
-- https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
-- See also Theorem 5.8.4 of the HoTT Book.
--
-- The reason we have this formulation in the core library and not the
-- standard one is that this one is more direct to prove using that
-- unglue is an equivalence. The standard formulation can be found in
-- Cubical/Basics/Univalence.
--
EquivContr : ∀ {ℓ} (A : Set ℓ) → isContr (Σ[ T ∈ Set ℓ ] T ≃ A)
EquivContr {ℓ} A =
  ( ( A , idEquiv A)
  , λ w i → let f : PartialP (~ i ∨ i) (λ x → Σ[ T ∈ Set ℓ ] T ≃ A)
                f = λ { (i = i0) → A , idEquiv A ; (i = i1) → w }
            in ( Glue A f , unglueEquiv _ _ f) )
