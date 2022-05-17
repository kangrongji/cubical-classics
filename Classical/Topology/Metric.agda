{-

Metric Spaces

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Metric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Topology.Base
open import Classical.Topology.Properties

open import Classical.Algebra.OrderedField
open import Classical.Analysis.Real

private
  variable
    ℓ : Level


module Metric (decide : LEM) where

  open Powerset decide
  open Topology decide
  open TopologicalSpace

  open Real decide
  open OrderedFieldStr (ℝCompleteOrderedField .fst)

  record MetricSpace (ℓ : Level) : Type (ℓ-suc ℓ) where
    field
      set   : Type ℓ
      isset : isSet set

      dist : set → set → ℝ
      dist-id : (x y : set) → dist x y ≡ 0 → x ≡ y
      dist-refl : (x y : set) → x ≡ y → dist x y ≡ 0
      dist-symm : (x y : set) → dist x y ≡ dist y x
      dist-Δ : (x y z : set) → dist x y + dist y z ≥ dist x z
