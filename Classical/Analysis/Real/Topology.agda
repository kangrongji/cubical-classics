{-

Topology of Real Numbers

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Topology where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Algebra.OrderedRing.AbsoluteValue
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Analysis.Real.Base

open import Classical.Topology.Base
open import Classical.Topology.Properties
open import Classical.Topology.Hausdorff
open import Classical.Topology.Metric


module TopologyOfReal (decide : LEM) where

  open Powerset    decide
  open Real        decide
  open AbsoluteValue   (ℝCompleteOrderedField .fst .fst)
  open OrderedFieldStr (ℝCompleteOrderedField .fst)
  open MetricStr   decide
  open TopologyStr decide
  open Hausdorff   decide
  open Topology
  open Metric


  -- ℝ is a metric space

  instance

    ℝMetric : Metric ℝ
    ℝMetric .dist x y = abs (x - y)
    ℝMetric .dist-id _ _ d≡0 = diff≡0→x≡y (abs≡0→x≡0 d≡0)
    ℝMetric .dist-refl _ _ x≡y = x≡0→abs≡0 (x≡y→diff≡0 x≡y)
    ℝMetric .dist-symm _ _ = absx≡→abs-x ∙ cong abs (sym x-y≡-[y-x])
    ℝMetric .dist-Δ _ _ _ = Δ-Inequality

    ℝTopology : Topology ℝ
    ℝTopology = MetricTopology


  -- ℝ is Hausdorff space

  isHausdorffℝ : isHausdorff ⦃ ℝTopology ⦄
  isHausdorffℝ = isHausdorffMetric
