{-

The Real Number ℝ

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Base where

open import Cubical.Foundations.Prelude
open import Classical.Axioms.ExcludedMiddle
open import Classical.Preliminary.QuoQ
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Algebra.OrderedField.Completion


module Real (decide : LEM) where

  open CompleteOrderedField decide
  open Completion decide

  abstract

    ℝ : CompleteOrderedField ℓ-zero ℓ-zero
    ℝ = complete ℚOrderedField isArchimedeanℚ
