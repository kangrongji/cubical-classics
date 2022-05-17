{-

Topology of Real Numbers

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Topology where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order
  using () renaming (_>_ to _>ℕ_ ; _<_ to _<ℕ_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Analysis.Real.Base

open import Classical.Topology.Base
open import Classical.Topology.Properties


module TopologyOfReal (decide : LEM) where

  open Real decide
  open OrderedFieldStr (ℝCompleteOrderedField .fst)

  open Powerset decide


