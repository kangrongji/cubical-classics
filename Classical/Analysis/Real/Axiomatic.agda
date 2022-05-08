{-

The Axioms of Real Number

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Axiomatic where

open import Cubical.Foundations.Prelude
open import Classical.Axioms.ExcludedMiddle
open import Classical.Preliminary.QuoQ
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Algebra.OrderedField.Completion


module AxiomsOfRealNumber (decide : LEM) where

  open CompleteOrderedField decide
  open Completion decide


  record Reals : Type (ℓ-suc ℓ-zero) where
    field
      complete-ordered-field : CompleteOrderedField ℓ-zero ℓ-zero


