{-

The Real Number

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Analysis.Real.Completeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.Rationals.QuoQ
  renaming (_-_ to _-ℚ_)

open import Classical.Preliminary.Rational
  renaming (_≤_ to _≤ℚ_ ; _<_ to _<ℚ_ ; _>_ to _>ℚ_)
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Analysis.Real.Base


module Completeness (decide : LEM) where

  open Powerset decide
  open Real     decide

  open DedekindCut

  _≤_ : ℝ → ℝ → Type
  _≤_ = {!!}

  _>_ : ℝ → ℝ → Type
  _>_ = {!!}

  _<_ : ℝ → ℝ → Type
  _<_ = {!!}

  _-_ : ℝ → ℝ → ℝ
  _-_ = {!!}

  infix 20 _-_
  infix 4  _<_

  record Sup (A : ℙ ℝ) : Type where
    field
      sup : ℝ
      upper-bound : (r : ℝ) → r ∈ A → r ≤ sup
      least : ∥ ((ε : ℝ) → ε > 0 → Σ[ r ∈ ℝ ] r ∈ A × (sup - ε < r)) ∥

  isBounded : ℙ ℝ → Type
  isBounded A = ∥ Σ[ b ∈ ℝ ] ((r : ℝ) → r ∈ A → r ≤ b) ∥

  -- The Supremum Principle/Dedekind Completeness of Real Numbers

  sup : {A : ℙ ℝ} → isBounded A → Sup A
  sup = {!!}
