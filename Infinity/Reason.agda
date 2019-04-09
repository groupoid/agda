{-# OPTIONS --cubical --safe #-}

module Infinity.Reason where

open import Agda.Builtin.Cubical.Glue using (_≃_)

open import Infinity.Core
open import Infinity.Path
open import Infinity.Equiv

module Reason-≡ {A : Set ℓ} where
  infix  1 begin
  infixr 10 _≡⟨⟩_ _≡⟨_⟩_
  infix  15 _∎
  
  begin : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = compPath x≡y y≡z

  _∎ : (x : A) → x ≡ x
  _ ∎ = refl

open Reason-≡ public

-- module Reason-≃ where 
--   infix  3 _≃-qed _□
--   infixr 2 _≃⟨⟩_ _≃⟨_⟩_
--   infix  1 ≃-proof_ begin≃_
  
--   ≃-proof_ begin≃_ : {x y : Set ℓ} → x ≃ y → x ≃ y
--   ≃-proof x≃y = x≃y
--   begin≃_ = ≃-proof_

--   _≃⟨⟩_ : (x {y} : Set ℓ) → x ≃ y → x ≃ y
--   _ ≃⟨⟩ x≡y = x≡y

--   _≃⟨_⟩_ : (x {y z} : Set ℓ) → x ≃ y → y ≃ z → x ≃ z
--   _ ≃⟨ x≃y ⟩ y≃z = compEquiv x≃y y≃z

--   _≃-qed _□ : (x : Set ℓ) → x ≃ x
--   x ≃-qed  = 
--   _□ = _≃-qed

-- open Reason-≃ public
