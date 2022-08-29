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
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary

open import Classical.Axioms
open import Classical.Foundations.Powerset

open import Classical.Topology.Base
open import Classical.Topology.Properties
open import Classical.Topology.Neighbourhood

private
  variable
    ℓ : Level


module _ ⦃ 🤖 : Oracle ⦄ where

  open Topology


  -- As is usually formulated, a topological space X is Hausdorff,
  -- if any two different points x y of X merely have neighbourhoods that do not intersect.

  record isHausdorff {X : Type ℓ} ⦃ 𝒯 : Topology X ⦄ : Type ℓ where
    field
      separate : {x y : X} → ¬ x ≡ y → ∥ Σ[ U ∈ ℙ X ] Σ[ V ∈ ℙ X ] (U ∈ ℕbh x) × (V ∈ ℕbh y) × (U ∩ V ≡ ∅) ∥₁


  module _ {X : Type ℓ} ⦃ 𝒯 : Topology X ⦄ ⦃ haus : isHausdorff ⦄ where

      open isHausdorff haus

      {-

        Corollaries of Hausdorff-ness

      -}

      -- In a Hausdorff space X,
      -- point x ∈ X and subset K ⊆ X are separating by open sets
      -- if x ∉ K and K is compact.

      sepOpenCompact : {x : X}{K : ℙ X} → isCompactSub K → x ∉ K → SepOpen x K
      sepOpenCompact {x = x₀} {K = K} takefin x₀∉K = sepOpen
        where
        P : ℙ X → hProp _
        P U = ∥ Σ[ x ∈ X ] (x ∈ K) × (U ∈ ℕbh x) × (Sep x₀ U) ∥₁ , squash₁

        𝒰 : ℙ ℙ X
        𝒰 = specify P

        𝒰⊆Open : 𝒰 ⊆ Open
        𝒰⊆Open p =
          Prop.rec (isProp∈ Open) (λ (_ , _ , q , _) → N∈ℕbhx→N∈Open q) (∈→Inhab P p)

        𝕌 : ℙ X
        𝕌 = union 𝒰

        -- A shuffle of propositions
        K⊆𝕌 : K ⊆ 𝕌
        K⊆𝕌 x∈K =
          proof _ , isProp∈ 𝕌 by do
          (U , V , U∈ℕx , V∈ℕx₀ , U∩V≡∅) ← separate (∈∉→≢ x∈K x₀∉K)
          return
            (∃→∈union ∣ U , N∈ℕbhx→x∈N U∈ℕx , Inhab→∈ P ∣ _ , x∈K , U∈ℕx , ∣ V , V∈ℕx₀ , U∩V≡∅ ∣₁ ∣₁ ∣₁)

        𝒰-covers-K : 𝒰 covers K
        𝒰-covers-K = K⊆𝕌 , 𝒰⊆Open

        𝕌∈Open : 𝕌 ∈ Open
        𝕌∈Open = union∈Open 𝒰⊆Open

        -- Another shuffle of propositions
        ∃𝒰₀ : ∥ Σ[ 𝒰₀ ∈ ℙ ℙ X ] 𝒰₀ ⊆ Open × isFinSub 𝒰₀ × 𝒰₀ covers K × ((U : ℙ X) → U ∈ 𝒰₀ → Sep x₀ U) ∥₁
        ∃𝒰₀ = do
          (𝒰₀ , 𝒰₀⊆𝒰 , fin𝒰₀ , 𝒰₀covK) ← takefin 𝒰-covers-K
          return (
            𝒰₀ , ⊆-trans {C = Open} 𝒰₀⊆𝒰 𝒰⊆Open , fin𝒰₀ , 𝒰₀covK ,
            λ U U∈𝒰₀ → Prop.rec squash₁ (λ (_ , _ , _ , sep) → sep) (∈→Inhab P (∈⊆-trans {B = 𝒰} U∈𝒰₀ 𝒰₀⊆𝒰)))

        sepOpen : SepOpen x₀ K
        sepOpen = do
          (_ , 𝒰₀⊆Open , fin⊆𝒰₀ , 𝒰₀covK , sep) ← ∃𝒰₀
          SepOpen⊆ (union∈Open 𝒰₀⊆Open) (𝒰₀covK .fst) (unionSep _ _ 𝒰₀⊆Open sep fin⊆𝒰₀)


      -- Compact subset of Hausdorff space is closed.

      isCompactSub→isClosedSub : {K : ℙ X} → isCompactSub K → isClosedSub K
      isCompactSub→isClosedSub takefin =
        SepCriterionOfClosedness (λ _ x∉K → SepOpen→Sep (sepOpenCompact takefin x∉K))
