{-

Metric Spaces

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Metric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as Empty
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


module MetricStr (decide : LEM) where

  open Powerset    decide
  open Real        decide
  open OrderedFieldStr (ℝCompleteOrderedField .fst)
  open TopologyStr decide
  open Topology

  record Metric (X : Type ℓ) : Type (ℓ-suc ℓ) where
    field
      dist : X → X → ℝ
      dist-id : (x y : X) → dist x y ≡ 0 → x ≡ y
      dist-refl : (x y : X) → x ≡ y → dist x y ≡ 0
      dist-symm : (x y : X) → dist x y ≡ dist y x
      dist-Δ : (x y z : X) → dist x y + dist y z ≥ dist x z

  open Metric


  module _ {X : Type ℓ} ⦃ 𝓂 : Metric X ⦄ where

    -- Open ball with center x and radius r

    module _ (x : X)(r : ℝ) ⦃ r>0 : r > 0 ⦄ where

      ball-prop : X → hProp _
      ball-prop y = (𝓂 .dist x y < r) , isProp<

      ℬ : ℙ X
      ℬ = specify ball-prop


    Inhab→∈ℬ : {x y : X}{r : ℝ} ⦃ r>0 : r > 0 ⦄ → 𝓂 .dist x y < r → y ∈ ℬ x r
    Inhab→∈ℬ {x = x} {r = r} = Inhab→∈ (ball-prop x r)

    ∈→Inhabℬ : {x y : X}{r : ℝ} ⦃ r>0 : r > 0 ⦄ → y ∈ ℬ x r → 𝓂 .dist x y < r
    ∈→Inhabℬ {x = x} {r = r} = ∈→Inhab (ball-prop x r)

    ℬ⊆ : {x : X}{r r' : ℝ} ⦃ _ : r > 0 ⦄ ⦃ _ : r' > 0 ⦄ → r < r' → ℬ x r ⊆ ℬ x r'
    ℬ⊆ r<r' x∈ℬxr = Inhab→∈ℬ (<-trans (∈→Inhabℬ x∈ℬxr) r<r')


    𝓂-prop : ℙ X → hProp _
    𝓂-prop A = ((x : X) → x ∈ A → ∥ Σ[ r ∈ ℝ ] Σ[ r>0 ∈ r > 0 ] ℬ x r ⦃ r>0 ⦄ ⊆ A ∥) , isPropΠ2 (λ _ _ → squash)

    Metric→Topology : Topology X
    Metric→Topology .openset = specify 𝓂-prop
    Metric→Topology .has-∅ = Inhab→∈ 𝓂-prop (λ x x∈∅ → Empty.rec (¬x∈∅ x x∈∅))
    Metric→Topology .has-total = Inhab→∈ 𝓂-prop (λ x _ → ∣ 1 , 1>0 , A⊆total {A = ℬ x 1 ⦃ 1>0 ⦄} ∣)
    Metric→Topology .∩-close {A = A} {B = B} A∈Open B∈Open =
      Inhab→∈ 𝓂-prop (λ x x∈A∩B → Prop.map2
      (λ (r₀ , r₀>0 , ℬxr₀⊆A) (r₁ , r₁>0 , ℬxr₁⊆B) →
        let (r , r>0 , r<r₀ , r<r₁) = min2 r₀>0 r₁>0 in
        r , r>0 , ⊆→⊆∩ A B
        (⊆-trans {A = ℬ x r ⦃ r>0 ⦄} (ℬ⊆ ⦃ r>0 ⦄ ⦃ r₀>0 ⦄ r<r₀) ℬxr₀⊆A)
        (⊆-trans {A = ℬ x r ⦃ r>0 ⦄} (ℬ⊆ ⦃ r>0 ⦄ ⦃ r₁>0 ⦄ r<r₁) ℬxr₁⊆B))
      (∈→Inhab 𝓂-prop A∈Open x (left∈-∩  A B x∈A∩B))
      (∈→Inhab 𝓂-prop B∈Open x (right∈-∩ A B x∈A∩B)))
    Metric→Topology .∪-close {S = S} S⊆Open =
      Inhab→∈ 𝓂-prop (λ x x∈∪S →
      Prop.rec squash
      (λ (A , x∈A , A∈S) → Prop.map
        (λ (r , r>0 , ℬxr⊆A) →
          r , r>0 , (λ p → ⊆union ℬxr⊆A A∈S p))
        (∈→Inhab 𝓂-prop (S⊆Open A∈S) x x∈A))
      (∈union→∃ x∈∪S))

    instance
      _ : Topology X
      _ = Metric→Topology
