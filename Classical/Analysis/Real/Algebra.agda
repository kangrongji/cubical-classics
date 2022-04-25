{-

The Real Number

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Analysis.Real.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.Rationals.QuoQ

open import Classical.Preliminary.Rational
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Analysis.Real.Base


module ℝAlgebra (decide : LEM) where

  open Powerset decide
  open Real     decide

  open DedekindCut

  _+ℝ_ : ℝ → ℝ → ℝ
  (a +ℝ b) .upper = specify (λ r → ∥ Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ] p ∈ a .upper × q ∈ b .upper × (r ≡ p + q) ∥ , squash)
