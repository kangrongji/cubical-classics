{-

Dedekind Completion of Archimedean Ordered Field

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Completion where

open import Cubical.Foundations.Prelude
open import Classical.Axioms.ExcludedMiddle
open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField.Base
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Algebra.OrderedField.DedekindCut.Completeness

private
  variable
    ℓ ℓ' : Level


module Completion (decide : LEM) where

  open CompleteOrderedField decide
  open Completeness

  complete : (𝒦 : OrderedField ℓ ℓ') → isArchimedean (𝒦 .fst) → CompleteOrderedField (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  complete 𝒦 archimedes = 𝕂CompleteOrderedField decide 𝒦 archimedes
