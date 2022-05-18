{-

Topology on a Type and Topological Space

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Base where

open import Cubical.Foundations.Prelude

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

private
  variable
    ℓ ℓ' : Level


module TopologyStr (decide : LEM) where

  open Powerset decide


  record Topology (X : Type ℓ) : Type (ℓ-suc ℓ) where
    no-eta-equality
    field
      openset : ℙ (ℙ X)
      has-∅     : ∅     ∈ openset
      has-total : total ∈ openset
      ∩-close : {A B : ℙ X}   → A ∈ openset → B ∈ openset → A ∩ B ∈ openset
      ∪-close : {S : ℙ (ℙ X)} → S ⊆ openset → union S ∈ openset


  record TopologicalSpace (ℓ : Level) : Type (ℓ-suc ℓ) where
    no-eta-equality
    field
      set   : Type ℓ
      isset : isSet set
      top   : Topology set
