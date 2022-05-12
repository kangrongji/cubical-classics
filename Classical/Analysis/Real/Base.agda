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
open import Classical.Analysis.Real.Axiomatic


module Real (decide : LEM) where

  open CompleteOrderedField decide
  open AxiomsOfRealNumber   decide
  open Reals

  abstract

    ℝ : CompleteOrderedField ℓ-zero ℓ-zero
    ℝ = isContrReals .fst .cof
