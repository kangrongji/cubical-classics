{-

Topological Space

-}
{-# OPTIONS --safe #-}
module Classics.Topology.Base where

open import Cubical.Foundations.Prelude

open import Classics.Axioms.ExcludedMiddle
open import Classics.Foundations.Powerset

private
  variable
    ℓ ℓ' : Level


module Topology (decide : LEM) where

  open Powerset decide

  record TopologicalSpace (ℓ : Level) : Type (ℓ-suc ℓ) where
    field
      set   : Type ℓ
      isset : isSet set
      openset : ℙ (ℙ set)
      has-∅     : ∅     ∈ openset
      has-total : total ∈ openset
      ∩-close : {A B : ℙ set}   → A ∈ openset → B ∈ openset → A ∩ B ∈ openset
      ∪-close : {S : ℙ (ℙ set)} → S ⊆ openset → union S ∈ openset

  open TopologicalSpace

  record ContinuousMap {ℓ ℓ' : Level}
    (X : TopologicalSpace ℓ)(Y : TopologicalSpace ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      map : X .set → Y .set
      presopen : (U : ℙ (Y .set)) → U ∈ Y .openset → preimage map U ∈ X .openset

  open ContinuousMap
