{-

Topology of Real Numbers

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Topology where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Algebra.OrderedRing.AbsoluteValue
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Extremum
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Analysis.Real.Base

open import Classical.Topology.Base
open import Classical.Topology.Properties
open import Classical.Topology.Hausdorff
open import Classical.Topology.Metric


module TopologyOfReal (decide : LEM) where

  open Powerset decide renaming ([_] to [[_]])
  open Real     decide
  open AbsoluteValue   (ℝCompleteOrderedField .fst .fst)
  open OrderedFieldStr (ℝCompleteOrderedField .fst)
  open MetricStr   decide
  open TopologyStr decide
  open TopologyProperties decide
  open Hausdorff   decide
  open Topology
  open Metric

  private
    variable
      x y z : ℝ


  -- ℝ is a metric space

  instance

    ℝMetric : Metric ℝ
    ℝMetric .dist x y = abs (x - y)
    ℝMetric .dist-id _ _ d≡0 = diff≡0→x≡y (abs≡0→x≡0 d≡0)
    ℝMetric .dist-refl _ _ x≡y = x≡0→abs≡0 (x≡y→diff≡0 x≡y)
    ℝMetric .dist-symm _ _ = absx≡→abs-x ∙ cong abs (sym x-y≡-[y-x])
    ℝMetric .dist-Δ _ _ _ = Δ-Inequality

    ℝTopology : Topology ℝ
    ℝTopology = Metric→Topology ⦃ ℝMetric ⦄


  -- ℝ is Hausdorff space

  isHausdorffℝ : isHausdorff ⦃ ℝTopology ⦄
  isHausdorffℝ = isHausdorffMetric


  -- Closed interval

  module _ (a b : ℝ) ⦃ a≤b : a ≤ b ⦄ where

    𝐈-prop : ℝ → hProp _
    𝐈-prop x = (a ≤ x) × (x ≤ b) , isProp× isProp≤ isProp≤

    [_,_] : ℙ ℝ
    [_,_] = specify 𝐈-prop

    instance
      a∈𝐈 : a ∈ [_,_]
      a∈𝐈 = Inhab→∈ 𝐈-prop (inr refl , a≤b)

      b∈𝐈 : b ∈ [_,_]
      b∈𝐈 = Inhab→∈ 𝐈-prop (a≤b , inr refl)


  module _ {a b : ℝ} ⦃ a≤b : a ≤ b ⦄ where

    Inhab→∈𝐈 : a ≤ x → x ≤ b → x ∈ [ a , b ]
    Inhab→∈𝐈 = {!!}

    ∈→Inhab𝐈-L : x ∈ [ a , b ] → a ≤ x
    ∈→Inhab𝐈-L = {!!}

    ∈→Inhab𝐈-R : x ∈ [ a , b ] → x ≤ b
    ∈→Inhab𝐈-R  = {!!}


  instance
    _ : 0 ≤ 1
    _ = inl 1>0

  Unit𝐈 : ℙ ℝ
  Unit𝐈 = [ 0 , 1 ]


  module _ (a b : ℝ) ⦃ a≤b : a ≤ b ⦄ where

    isClosedInterval : isClosedSubSet [ a , b ]
    isClosedInterval = {!!}

    isCompactInterval : isCompactSubset [ a , b ]
    isCompactInterval = {!!}
      where

      module _ {𝒰 : ℙ Subset}(𝒰cov𝐈 : 𝒰 covers [ a , b ]) where

        open Extremum decide (ℝCompleteOrderedField .fst)
        open Supremum

        getSup = ℝCompleteOrderedField .snd

        cov-prop : ℝ → hProp _
        cov-prop x =
          (Σ[ x∈𝐈 ∈ x ∈ [ a , b ] ]
            ∥ Σ[ 𝒰₀ ∈ ℙ (ℙ ℝ) ] 𝒰₀ ⊆ 𝒰 × isFinSubset 𝒰₀ × 𝒰₀ covers [ a , x ] ⦃ ∈→Inhab𝐈-L x∈𝐈 ⦄ ∥) ,
          {!!}

        cov-sub = specify cov-prop

        cov-sup : Supremum cov-sub
        cov-sup = getSup {!!} {!!}

        x₀ = cov-sup .sup

        x₀≥a : x₀ ≥ a
        x₀≥a = {!!}

        x₀≤b : x₀ ≤ b
        x₀≤b = {!!}

        module _
          (U : ℙ ℝ)(r : ℝ) ⦃ r>0 : r > 0 ⦄
          (U∈𝒰 : U ∈ 𝒰)(ℬx₀r⊆U : ℬ x₀ r ⊆ U) where

          ε : ℝ
          ε = 2

          ε/2 = middle 0 ε

          ε/2>0 : ε/2 > 0
          ε/2>0 = {!!}

          a≤x₀+ε/2 : a ≤ x₀ + ε/2
          a≤x₀+ε/2 = {!!}

          x₀+ε/2≤b : x₀ + ε/2 ≤ b
          x₀+ε/2≤b = {!!}

          x₀+ε/2∈𝐈 : (x₀ + ε/2) ∈ [ a , b ]
          x₀+ε/2∈𝐈 = {!!}

          instance
            ε>0 : ε > 0
            ε>0 = {!!}

            a≤x₀-ε : a ≤ x₀ - ε
            a≤x₀-ε = {!!}

            _ : a ≤ x₀ + ε/2
            _ = ∈→Inhab𝐈-L x₀+ε/2∈𝐈

            x₀-ε∈𝐈 : (x₀ - ε) ∈ [ a , b ]
            x₀-ε∈𝐈 = {!!}

          ε/2<ε = middle<r ε>0

          ∃𝒰₀ : ∥ Σ[ 𝒰₀ ∈ ℙ ℙ ℝ ] 𝒰₀ ⊆ 𝒰 × isFinSubset 𝒰₀ × 𝒰₀ covers [ a , x₀ - ε ] ∥
          ∃𝒰₀ = {!!}

          ∃V : ∥ Σ[ V ∈ ℙ ℝ ] V ∈ 𝒰 × ℬ x₀ ε ⦃ ε>0 ⦄ ⊆ V ∥
          ∃V = {!!}

          module _
            (𝒰₀ : ℙ ℙ ℝ)(𝒰₀⊆𝒰 : 𝒰₀ ⊆ 𝒰)(fin𝒰₀ : isFinSubset 𝒰₀)(cov : 𝒰₀ covers [ a , x₀ - ε ])
            (V : ℙ ℝ)(V∈𝒰 : V ∈ 𝒰)(ℬx₀ε⊆V : ℬ x₀ ε ⊆ V) where

            𝒰₀+V : ℙ ℙ ℝ
            𝒰₀+V = 𝒰₀ ∪ [[ V ]]

            𝒰₀+V∈𝒰 : 𝒰₀+V ⊆ 𝒰
            𝒰₀+V∈𝒰 = ⊆→⊆∪ {C = 𝒰} 𝒰₀⊆𝒰 (A∈S→[A]⊆S {S = 𝒰} V∈𝒰)

            fin𝒰₀+V : isFinSubset 𝒰₀+V
            fin𝒰₀+V = isfinsuc V fin𝒰₀

            ∪-helper : {x : ℝ} → (x ∈ union 𝒰₀) ⊎ (x ∈ V) → x ∈ union 𝒰₀+V
            ∪-helper (inl x∈∪𝒰₀) = union∪-left⊆ x∈∪𝒰₀
            ∪-helper {x = x} (inr x∈[V]) = union∪-right⊆ (subst (x ∈_) (sym union[A]) x∈[V])

            covMore : 𝒰₀+V covers [ a , x₀ + ε/2 ]
            covMore .fst {x = x} x∈[a,x₀+ε/2] = case-split (<≤-total (x₀ - ε) x)
              where
              case-split : _ → _
              case-split (inl x>x₀-ε) = ∪-helper (inr (ℬx₀ε⊆V x∈ℬx₀ε))
                where
                x∈ℬx₀ε : x ∈ ℬ x₀ ε
                x∈ℬx₀ε = Inhab→∈ℬ (absInOpenInterval ε>0 x>x₀-ε
                  (≤<-trans (∈→Inhab𝐈-R x∈[a,x₀+ε/2]) (+-lPres< ε/2<ε)))
              case-split (inr x≤x₀-ε) = ∪-helper (inl (cov .fst x∈[a,x₀-ε]))
                where
                x∈[a,x₀-ε] : x ∈ [ a , x₀ - ε ]
                x∈[a,x₀-ε] = Inhab→∈𝐈 (∈→Inhab𝐈-L x∈[a,x₀+ε/2]) x≤x₀-ε
            covMore .snd = ⊆-trans {A = 𝒰₀+V} 𝒰₀+V∈𝒰 (𝒰cov𝐈 .snd)

            no-way' : ⊥
            no-way' = <≤-asym (+-rPos→> ε/2>0) (cov-sup .bound _ x₀+ε/2∈cov)
              where
              x₀+ε/2∈cov : (x₀ + ε/2) ∈ cov-sub
              x₀+ε/2∈cov = Inhab→∈ cov-prop (x₀+ε/2∈𝐈 , ∣ 𝒰₀+V , 𝒰₀+V∈𝒰 , fin𝒰₀+V , covMore ∣)


        module _ (x₀<b : x₀ < b) where

          ∃ℬ : ∥ Σ[ U ∈ ℙ ℝ ] Σ[ r ∈ ℝ ] Σ[ r>0 ∈ r > 0 ] (U ∈ 𝒰) × (ℬ x₀ r ⦃ r>0 ⦄ ⊆ U) ∥
          ∃ℬ = {!!}

          --∃𝒰₀ : ∥

          ¬x₀<b : ⊥
          ¬x₀<b = {!!}
