{-# OPTIONS --cubical --safe #-}

module Infinity.Algebra.Hopf where

open import Infinity.Core public
open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Path
open import Infinity.Equiv public
open import Infinity.Univ
open import Infinity.HIT.S1
open import Infinity.HIT.S2
open import Infinity.HIT.Susp

HopfS² : S² → Set
HopfS²  base      = S¹
HopfS² (surf i j) = Glue S¹ (λ { (i = i0) → _ , idEquiv S¹
                               ; (i = i1) → _ , idEquiv S¹
                               ; (j = i0) → _ , idEquiv S¹
                               ; (j = i1) → _ , _ , rotIsEquiv (loop i) } )

HopfS²' : S² → Set
HopfS²'  base      = S¹
HopfS²' (surf i j) = Glue S¹ (λ { (i = i0) → _ , rotLoopEquiv i0
                                ; (i = i1) → _ , rotLoopEquiv i0
                                ; (j = i0) → _ , rotLoopEquiv i0
                                ; (j = i1) → _ , rotLoopEquiv i } )

HopfSuspS¹ : SuspS¹ → Set
HopfSuspS¹  north      = S¹
HopfSuspS¹  south      = S¹
HopfSuspS¹ (merid x i) = ua (_ , rotIsEquiv x) i

