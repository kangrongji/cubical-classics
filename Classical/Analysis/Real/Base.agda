{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Base where

open import Cubical.Foundations.Prelude
open import Classical.Axioms.ExcludedMiddle
open import Classical.Preliminary.QuoQ
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Completion


module Real (decide : LEM) where

  open Completion decide

  abstract

    ℝ : OrderedField ℓ-zero ℓ-zero
    ℝ = complete ℚOrderedField isArchimedeanℚ
