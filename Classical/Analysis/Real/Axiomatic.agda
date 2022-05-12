{-

The Axioms of Real Number

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Axiomatic where

open import Cubical.Foundations.Prelude
open import Classical.Axioms.ExcludedMiddle
open import Classical.Preliminary.QuoQ
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Morphism
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Algebra.OrderedField.Completion


module AxiomsOfRealNumber (decide : LEM) where

  open CompleteOrderedField decide

  -- Real Number is a complete ordered field as is usually defined in classical mathematics.

  record Reals : Type (ℓ-suc ℓ-zero) where
    field
      cof : CompleteOrderedField ℓ-zero ℓ-zero

  open Reals


  open InclusionFromℚ
  open Completion decide ℚOrderedField isArchimedeanℚ

  -- The Existence and Uniqueness of Real Number

  isContrReals : isContr Reals
  isContrReals .fst .cof = complete
  isContrReals .snd 𝒦 i .cof =
    uaCompleteOrderedField complete (𝒦 .cof) (extend (𝒦 .cof) (ℚ→KOrderedFieldHom (𝒦 .cof .fst))) i
