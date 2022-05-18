{-

Hausdorff Space

This file contains:
- Definition of Hausdorff space;
- Point and compact subset can be separated by open set in Hausdorff space;
- Compact subset in Hausdorff space is closed.

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Hausdorff where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Topology.Base
open import Classical.Topology.Properties
open import Classical.Topology.Neighbourhood

private
  variable
    ℓ : Level


module Hausdorff (decide : LEM) where

  open Powerset      decide
  open TopologyStr   decide
  open TopologyProperties decide
  open Neighbourhood decide
  open Topology


  module _ {X : Type ℓ} ⦃ 𝒯 : Topology X ⦄ where

    -- The Hausdorff Separation Axiom

    isHausdorff : Type _
    isHausdorff =
      {x y : X} → ¬ x ≡ y → ∥ Σ[ U ∈ ℙ X ] Σ[ V ∈ ℙ X ] (U ∈ ℕbh x) × (V ∈ ℕbh y) × (U ∩ V ≡ ∅) ∥


    module _
      (separate : isHausdorff) where

      -- In a Hausdorff space X,
      -- point x ∈ X and subset K ⊆ X are separating by open sets
      -- if x ∉ K and K is compact.

      sepOpenCompact : {x : X}{K : Subset} → isCompactSubset K → x ∉ K → SepOpen x K
      sepOpenCompact {x = x₀} {K = K} takefin x₀∉K = sepOpen
        where
        P : Subset → hProp _
        P U = ∥ Σ[ x ∈ X ] (x ∈ K) × (U ∈ ℕbh x) × (Sep x₀ U) ∥ , squash

        𝒰 : ℙ Subset
        𝒰 = specify P

        𝒰⊆Open : 𝒰 ⊆ Open
        𝒰⊆Open p =
          Prop.rec (isProp∈ Open) (λ (_ , _ , q , _) → N∈ℕbhx→N∈Open q) (∈→Inhab P p)

        𝕌 : Subset
        𝕌 = union 𝒰

        -- A shuffle of propositions
        K⊆𝕌 : K ⊆ 𝕌
        K⊆𝕌 x∈K =
          Prop.rec (isProp∈ 𝕌)
          (λ (U , V , U∈ℕx , V∈ℕx₀ , U∩V≡∅) →
             ∃→∈union ∣ U , N∈ℕbhx→x∈N U∈ℕx , Inhab→∈ P ∣ _ , x∈K , U∈ℕx , ∣ V , V∈ℕx₀ , U∩V≡∅ ∣ ∣ ∣)
          (separate (∈∉→≢ x∈K x₀∉K))

        𝒰-covers-K : 𝒰 covers K
        𝒰-covers-K = K⊆𝕌 , 𝒰⊆Open

        𝕌∈Open : 𝕌 ∈ Open
        𝕌∈Open = union∈Open 𝒰⊆Open

        -- Another shuffle of propositions
        ∃𝒰₀ : ∥ Σ[ 𝒰₀ ∈ ℙ Subset ] 𝒰₀ ⊆ Open × isFinSubset 𝒰₀ × 𝒰₀ covers K × ((U : Subset) → U ∈ 𝒰₀ → Sep x₀ U) ∥
        ∃𝒰₀ =
          Prop.map
          (λ (𝒰₀ , 𝒰₀⊆𝒰 , fin𝒰₀ , 𝒰₀covK) →
              𝒰₀ , ⊆-trans {C = Open} 𝒰₀⊆𝒰 𝒰⊆Open , fin𝒰₀ , 𝒰₀covK ,
              λ U U∈𝒰₀ → Prop.rec squash (λ (_ , _ , _ , sep) → sep) (∈→Inhab P (∈⊆-trans {B = 𝒰} U∈𝒰₀ 𝒰₀⊆𝒰)))
          (takefin 𝒰-covers-K)

        sepOpen : SepOpen x₀ K
        sepOpen = Prop.rec squash
          (λ (_ , 𝒰₀⊆Open , fin⊆𝒰₀ , 𝒰₀covK , sep)
              →  SepOpen⊆ (union∈Open 𝒰₀⊆Open) (𝒰₀covK .fst) (unionSep _ _ 𝒰₀⊆Open sep fin⊆𝒰₀)) ∃𝒰₀


      -- Compact subset of Hausdorff space is closed.

      isCompactSubset→isClosedSubSet : {K : Subset} → isCompactSubset K → isClosedSubSet K
      isCompactSubset→isClosedSubSet takefin =
        SepCriterionOfClosedness (λ _ x∉K → SepOpen→Sep (sepOpenCompact takefin x∉K))
