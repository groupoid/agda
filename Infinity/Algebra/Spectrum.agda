{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Spectrum where 

open import Infinity.Proto hiding (_+_)
open import Infinity.Sigma
open import Infinity.Omega 
open import Infinity.Pointed 
open import Infinity.Inductive.Z

record Ω-Spectrum : Set (ℓ-succ ℓ) where
  constructor _⋊_
  field
    spect : (n : ℤ) → Set₊ ℓ
    chain : (n : ℤ) → (spect n) ≡ (Ω (spect (sucℤ n)))
open Ω-Spectrum

record Ω-Map (E F : Ω-Spectrum {ℓ}) : Set ℓ where
  field
    map : (n k : ℤ) → (spect E n) →₊ (spect F (n + k))
open Ω-Map

record Σ-Spectrum : Set (ℓ-succ ℓ) where
  constructor _⋉_ 
  field 
    spect :   (n : ℤ) → Set₊ ℓ
    chain : Σ[ n ∈ ℤ ] (spect n) ≡ spect (sucℤ n)
open Σ-Spectrum
    
record Σ-Map (S T : Σ-Spectrum {ℓ}) : Set ℓ where 
  field 
    map : Σ[ n ∈ ℤ ] (Σ[ k ∈ ℤ ] ((spect S n) →₊ (spect T (n + k))))
open Σ-Map
