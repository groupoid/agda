{-# OPTIONS --cubical --safe #-}

module Infinity.Spectrum where 

open import Infinity.Proto
open import Infinity.Pointed 
open import Infinity.Omega

record Ω-Spectrum : Set where
  constructor _⋊_
  field 
    spect : (n : ℕ) → Set₊
    chain : (n : ℕ) → (spect n) ≡ (Ω (spect (suc n)))
open Ω-Spectrum 

record Ω-Map (E F : Ω-Spectrum) : Set where
  field
    mp : (n k : ℕ) → Map₊ (spect E n) (spect F (n + k))
open Ω-Map
