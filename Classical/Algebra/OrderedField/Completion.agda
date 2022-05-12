{-

Dedekind Completion of Archimedean Ordered Field

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Algebra.OrderedField.Completion where

open import Cubical.Foundations.Prelude
open import Classical.Axioms.ExcludedMiddle
open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField.Base
open import Classical.Algebra.OrderedField.Morphism
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Algebra.OrderedField.DedekindCut.Completeness
open import Classical.Algebra.OrderedField.DedekindCut.UniversalProperty

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


module Completion (decide : LEM)
  (𝒦 : OrderedField ℓ ℓ')(archimedes : isArchimedean (𝒦 .fst)) where

  open CompleteOrderedField decide
  open Completeness
  open CompletenessOfCuts
  open UniversalProperty

  complete : CompleteOrderedField (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  complete = 𝕂CompleteOrderedField decide 𝒦 archimedes

  extend : (𝒦' : CompleteOrderedField ℓ'' ℓ''') → OrderedFieldHom 𝒦 (𝒦' .fst) → OrderedFieldHom (complete .fst) (𝒦' .fst)
  extend = extendedOrderedFieldHom decide 𝒦 archimedes
