{-

This file contains:
- The notion of closed subset;
- Definition and basic properties of open covering;
- Definition of compactness.

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Topology.Base

private
  variable
    ℓ : Level


module TopologyProperties (decide : LEM) where

  open Powerset    decide
  open TopologyStr decide
  open Topology


  module _ {X : Type ℓ} ⦃ 𝒯 : Topology X ⦄ where

    -- The ppen and closed subsets

    Subset : Type _
    Subset = ℙ X

    Open : ℙ Subset
    Open = 𝒯 .openset

    Closed : ℙ Subset
    Closed A = Open (∁ A)

    isOpenSubSet : Subset → Type _
    isOpenSubSet U = U ∈ Open

    isClosedSubSet : Subset → Type _
    isClosedSubSet A = ∁ A ∈ Open


    -- Open coverings

    _covers_ : ℙ Subset → Subset → Type _
    _covers_ 𝒰 A = A ⊆ union 𝒰 × 𝒰 ⊆ Open

    union∈Open : {𝒰 : ℙ Subset} → 𝒰 ⊆ Open → union 𝒰 ∈ Open
    union∈Open = 𝒯 .∪-close


    -- Compact subset

    isCompactSubset : Subset → Type _
    isCompactSubset K =
      {𝒰 : ℙ Subset} → 𝒰 covers K → ∥ Σ[ 𝒰₀ ∈ ℙ Subset ] 𝒰₀ ⊆ 𝒰 × isFinSubset 𝒰₀ × 𝒰₀ covers K ∥

    isCompact : Type _
    isCompact = isCompactSubset total
