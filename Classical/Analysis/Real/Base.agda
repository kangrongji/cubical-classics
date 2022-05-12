{-

The Real Number ℝ

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Literals public
open import Cubical.HITs.Rationals.QuoQ
open import Cubical.Algebra.Ring

open import Classical.Axioms.ExcludedMiddle
open import Classical.Preliminary.QuoQ
open import Classical.Algebra.OrderedRing
open import Classical.Algebra.OrderedRing.Morphism
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Morphism
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Analysis.Real.Axiomatic


module Real (decide : LEM) where

  open CompleteOrderedField decide
  open AxiomsOfRealNumber   decide
  open Reals

  open InclusionFromℚ
  open OrderedRingHom


  abstract

    ℝCompleteOrderedField : CompleteOrderedField ℓ-zero ℓ-zero
    ℝCompleteOrderedField = isContrReals .fst .cof

    ℚ→ℝOrderedFieldHom : OrderedFieldHom ℚOrderedField (ℝCompleteOrderedField .fst)
    ℚ→ℝOrderedFieldHom = ℚ→KOrderedFieldHom (ℝCompleteOrderedField .fst)


  ℝ : Type
  ℝ = ℝCompleteOrderedField .fst .fst .fst .fst

  ℚ→ℝ : ℚ → ℝ
  ℚ→ℝ = ℚ→ℝOrderedFieldHom .ring-hom .fst


  -- Natural number and negative integer literals for ℝ

  open OrderedRingStr (ℝCompleteOrderedField .fst .fst)

  instance
    fromNatℝ : HasFromNat ℝ
    fromNatℝ = record { Constraint = λ _ → Unit ; fromNat = λ n → ℕ→R-Pos n }

  instance
    fromNegℝ : HasFromNeg ℝ
    fromNegℝ = record { Constraint = λ _ → Unit ; fromNeg = λ n → ℕ→R-Neg n }
