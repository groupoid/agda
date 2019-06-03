{-# OPTIONS --cubical --safe #-}

module Infinity.Inductive.Permutation where

open import Infinity.Proto
open import Infinity.Inductive.List 
open import Infinity.Inductive.Nat

-- x ◂ xs ≡ ys means that ys is equal to xs with x inserted somewhere

module _ (A : Set ℓ) where 
    data _◂_≡_ (x : A) : List A → List A → Set ℓ where
      here  : ∀ {xs}           → x ◂ xs ≡ (x ∷ xs)
      there : ∀ {y} {xs} {xys} → (p : x ◂ xs ≡ xys) → x ◂ (y ∷ xs) ≡ (y ∷ xys)

    -- Proof that a list is a permutation of another one
    data IsPermutation : List A → List A → Set ℓ where
      []  : IsPermutation [] []
      _∷_ : ∀ {x xs ys xys} → (p : x ◂ ys ≡ xys) → (ps : IsPermutation xs ys) → IsPermutation (x ∷ xs) xys

    -- Identity permutation
    id-permutation : (xs : List A) → IsPermutation xs xs
    id-permutation []       = []
    id-permutation (_ ∷ xs) = here ∷ id-permutation xs

    -- cons on the other side
    insert-permutation : ∀ {x xs ys xys} → x ◂ ys ≡ xys → IsPermutation ys xs → IsPermutation xys (x ∷ xs)
    insert-permutation  here      p       = here    ∷ p
    insert-permutation (there y) (p ∷ ps) = there p ∷ insert-permutation y ps

    -- inverse permutations
    inverse-permutation : ∀ {xs ys} -> IsPermutation xs ys → IsPermutation ys xs
    inverse-permutation []       = []
    inverse-permutation (p ∷ ps) = insert-permutation p (inverse-permutation ps)
