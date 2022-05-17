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
open import Classical.Algebra.OrderedField.Completion


{-

  The Axioms of Real Number

-}

module AxiomsOfRealNumber (decide : LEM) where

  open CompleteOrderedField decide

  -- Real Number is a complete ordered field as is usually defined in classical mathematics.

  Reals : Type (ℓ-suc ℓ-zero)
  Reals = CompleteOrderedField ℓ-zero ℓ-zero

  open InclusionFromℚ
  open Completion decide ℚOrderedField isArchimedeanℚ

  -- The Existence and Uniqueness of Real Number

  isContrReals : isContr Reals
  isContrReals .fst = complete
  isContrReals .snd 𝒦 i = uaCompleteOrderedField complete 𝒦 (extend 𝒦 (ℚ→KOrderedFieldHom (𝒦 .fst))) i


{-

  Basics of Real Number

-}

module Real (decide : LEM) where

  open CompleteOrderedField decide
  open InclusionFromℚ
  open OrderedRingHom

  open AxiomsOfRealNumber   decide


  abstract

    ℝCompleteOrderedField : CompleteOrderedField ℓ-zero ℓ-zero
    ℝCompleteOrderedField = isContrReals .fst

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

{-
  open OrderedRingStr (ℚOrderedField .fst)

  instance
    fromNatℝ : HasFromNat ℝ
    fromNatℝ = record { Constraint = λ _ → Unit ; fromNat = λ n → ℚ→ℝ (ℕ→R-Pos n) }

  instance
    fromNegℝ : HasFromNeg ℝ
    fromNegℝ = record { Constraint = λ _ → Unit ; fromNeg = λ n → ℚ→ℝ (ℕ→R-Neg n) }
-}

  {-
  -- For the convenience of use, importing ordered structure publicly here

  open OrderedFieldStr (ℝCompleteOrderedField .fst) public -}
