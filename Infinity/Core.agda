{-# OPTIONS --cubical --safe #-}
module Infinity.Core where

open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public

open import Agda.Primitive.Cubical public
     renaming ( primIMin       to _∧_
              ; primIMax       to _∨_
              ; primINeg       to ~_
              ; isOneEmpty     to empty
              ; primHComp      to hcomp
              ; primTransp     to transp
              ; itIsOne        to 1=1 )

open import Agda.Primitive public
     using    ( Level ; _⊔_ )
     renaming ( lzero to ℓ-zero
              ; lsuc  to ℓ-suc )

infix 4 _[_≡_]

_[_≡_] : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
_[_≡_] = PathP

Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
Path A a b = PathP (λ _ → A) a b

{-
private

  sys : ∀ i → Partial (i ∨ ~ i) Set₁
  sys i (i = i0) = Set
  sys i (i = i1) = Set → Set

  sys' : ∀ i → Partial (i ∨ ~ i) Set₁
  sys' i = λ { (i = i0) → Set ; (i = i1) → Set → Set }

  sys2 : ∀ i j → Partial (i ∨ (i ∧ j)) Set₁
  sys2 i j = λ { (i = i1) → Set ; (i = i1) (j = i1) → Set }

  sys3 : Partial i0 Set₁
  sys3 = λ { () }
-}

_[_↦_] : ∀ {ℓ} (A : Set ℓ) (φ : I) (u : Partial φ A) → Agda.Primitive.Setω
A [ φ ↦ u ] = Sub A φ u

infix 4 _[_↦_]

ouc : ∀ {ℓ} {A : Set ℓ} {φ : I} {u : Partial φ A} → A [ φ ↦ u ] → A
ouc = primSubOut

hfill : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (i : I) → A
hfill {φ = φ} u u0 i = hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1 ; (i = i0) → ouc u0 }) (ouc u0)

comp : ∀ {ℓ : I → Level} (A : ∀ i → Set (ℓ i)) {φ : I} (u : ∀ i → Partial φ (A i)) (u0 : A i0 [ φ ↦ u i0 ]) → A i1
comp A {φ = φ} u u0 = hcomp (λ i → λ { (φ = i1) → transp (λ j → A (i ∨ j)) i (u _ 1=1) }) (transp A i0 (ouc u0))

fill : ∀ {ℓ : I → Level} (A : ∀ i → Set (ℓ i)) {φ : I} (u : ∀ i → Partial φ (A i)) (u0 : A i0 [ φ ↦ u i0 ]) → ∀ i →  A i
fill A {φ = φ} u u0 i = comp (λ j → A (i ∧ j))
       (λ j → λ { (φ = i1) → u (i ∧ j) 1=1 ; (i = i0) → ouc u0 }) (inc {φ = φ ∨ (~ i)} (ouc {φ = φ} u0))

transpFill : ∀ {ℓ} {A' : Set ℓ} (φ : I) (A : (i : I) → Set ℓ [ φ ↦ (λ _ → A') ])
             → (u0 : ouc (A i0)) → PathP (λ i → ouc (A i)) u0 (transp (λ i → ouc (A i)) φ u0)
transpFill φ A u0 i = transp (λ j → ouc (A (i ∧ j))) (~ i ∨ φ) u0
