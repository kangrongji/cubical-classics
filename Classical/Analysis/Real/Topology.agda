{-

Topology of Real Numbers

This file contains:
- The canonical metric of ℝ and its induced topology;
- Basics of closed interval;
- Basics of bounded subset of ℝ;
- The Heine-Borel theorem.

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


  {-

    Canonical Metric and Topology of ℝ

  -}

  -- ℝ is a metric space

  instance

    ℝMetric : Metric ℝ
    ℝMetric .dist x y = abs (x - y)
    ℝMetric .dist-id   d≡0 = diff≡0→x≡y (abs≡0→x≡0 d≡0)
    ℝMetric .dist-refl x≡y = x≡0→abs≡0 (x≡y→diff≡0 x≡y)
    ℝMetric .dist-symm _ _ = absx≡→abs-x ∙ cong abs (sym x-y≡-[y-x])
    ℝMetric .dist-Δ _ _ _ = Δ-Inequality

    ℝTopology : Topology ℝ
    ℝTopology = Metric→Topology ⦃ ℝMetric ⦄


  -- ℝ is Hausdorff space

  isHausdorffℝ : isHausdorff ⦃ ℝTopology ⦄
  isHausdorffℝ = isHausdorffMetric


  {-

    Closed Interval

  -}

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
    Inhab→∈𝐈 a≤x x≤b = Inhab→∈ (𝐈-prop a b) (a≤x , x≤b)

    ∈→Inhab𝐈-L : x ∈ [ a , b ] → a ≤ x
    ∈→Inhab𝐈-L x∈𝐈 = ∈→Inhab (𝐈-prop a b) x∈𝐈 .fst

    ∈→Inhab𝐈-R : x ∈ [ a , b ] → x ≤ b
    ∈→Inhab𝐈-R x∈𝐈 = ∈→Inhab (𝐈-prop a b) x∈𝐈 .snd

    x∈[a,b] : a ≡ b → x ∈ [ a , b ] → a ≡ x
    x∈[a,b] {x = x} a≡b x∈𝐈 = ≤-asym (∈→Inhab𝐈-L x∈𝐈) (subst (x ≤_) (sym a≡b) (∈→Inhab𝐈-R x∈𝐈))


  instance
    _ : 0 ≤ 1
    _ = inl 1>0

  Unit𝐈 : ℙ ℝ
  Unit𝐈 = [ 0 , 1 ]


  module _ (a b : ℝ) ⦃ a≤b : a ≤ b ⦄ where

    -- Closed interval is compact.

    isCompactInterval : isCompactSub [ a , b ]
    isCompactInterval = cov[a,b]
      where

      module _ {𝒰 : ℙ ℙ ℝ}(𝒰cov𝐈 : 𝒰 covers [ a , b ]) where

        open Extremum decide (ℝCompleteOrderedField .fst)
        open Supremum

        getSup = ℝCompleteOrderedField .snd

        cov-prop : ℝ → hProp _
        cov-prop x =
          (Σ[ x∈𝐈 ∈ x ∈ [ a , b ] ]
            ∥ Σ[ 𝒰₀ ∈ ℙ (ℙ ℝ) ] 𝒰₀ ⊆ 𝒰 × isFinSub 𝒰₀ × 𝒰₀ covers [ a , x ] ⦃ ∈→Inhab𝐈-L x∈𝐈 ⦄ ∥) ,
          isPropΣ (isProp∈ [ a , b ]) (λ _ → squash)

        cov-sub = specify cov-prop

        a≤x∈sub : (x : ℝ) → x ∈ cov-sub → x ≥ a
        a≤x∈sub x x∈sub = ∈→Inhab𝐈-L (∈→Inhab cov-prop x∈sub .fst)

        b≥x∈sub : (x : ℝ) → x ∈ cov-sub → x ≤ b
        b≥x∈sub x x∈sub =  ∈→Inhab𝐈-R (∈→Inhab cov-prop x∈sub .fst)

        instance
          a≤a : a ≤ a
          a≤a = inr refl

        cov-sup : Supremum cov-sub
        cov-sup = getSup ∣ a , Inhab→∈ cov-prop (a∈𝐈 a b , cov-a) ∣ ∣ b , b≥x∈sub ∣
          where
          cov-a : ∥ Σ[ 𝒰₀ ∈ ℙ (ℙ ℝ) ] 𝒰₀ ⊆ 𝒰 × isFinSub 𝒰₀ × 𝒰₀ covers [ a , a ] ⦃ ∈→Inhab𝐈-L (a∈𝐈 a b) ⦄ ∥
          cov-a = Prop.map
            (λ (U , a∈U , U∈𝒰) →
              [[ U ]] , A∈S→[A]⊆S U∈𝒰 , isFinSub[x] ,
              (λ {x} x∈[a,a] →
                let a≡x : a ≡ x
                    a≡x = x∈[a,b] refl x∈[a,a]
                in  subst (x ∈_) (sym union[A]) (subst (_∈ U) a≡x a∈U)) ,
              A∈S→[A]⊆S (𝒰cov𝐈 .snd U∈𝒰))
            (∈cover (a∈𝐈 a b) 𝒰cov𝐈)

        x₀ = cov-sup .sup

        instance
          x₀≥a : x₀ ≥ a
          x₀≥a = supLowerBounded _ cov-sup a≤x∈sub

        x₀≤b : x₀ ≤ b
        x₀≤b = supUpperBounded _ cov-sup b≥x∈sub

        x₀∈𝐈 : x₀ ∈ [ a , b ]
        x₀∈𝐈 = Inhab→∈𝐈 x₀≥a x₀≤b

        module _
          (U : ℙ ℝ)(r : ℝ) ⦃ r>0 : r > 0 ⦄ (U∈𝒰 : U ∈ 𝒰)(ℬx₀r⊆U : ℬ x₀ r ⊆ U)
          (y : ℝ)(x₀-r<y : x₀ - r < y)(y∈sub : y ∈ cov-sub) where

          instance
            a≤y : a ≤ y
            a≤y = a≤x∈sub y y∈sub

          module _
            (𝒰₀ : ℙ ℙ ℝ)(𝒰₀⊆𝒰 : 𝒰₀ ⊆ 𝒰)(fin𝒰₀ : isFinSub 𝒰₀)(cov : 𝒰₀ covers [ a , y ])
            where

            𝒰₀+U : ℙ ℙ ℝ
            𝒰₀+U = 𝒰₀ ∪ [[ U ]]

            𝒰₀+U∈𝒰 : 𝒰₀+U ⊆ 𝒰
            𝒰₀+U∈𝒰 = ⊆→⊆∪ {C = 𝒰} 𝒰₀⊆𝒰 (A∈S→[A]⊆S {S = 𝒰} U∈𝒰)

            fin𝒰₀+U : isFinSub 𝒰₀+U
            fin𝒰₀+U = isfinsuc fin𝒰₀ U

            ∪-helper : {x : ℝ} → (x ∈ union 𝒰₀) ⊎ (x ∈ U) → x ∈ union 𝒰₀+U
            ∪-helper (inl x∈∪𝒰₀) = union∪-left⊆ x∈∪𝒰₀
            ∪-helper {x = x} (inr x∈[U]) = union∪-right⊆ (subst (x ∈_) (sym union[A]) x∈[U])

            covSup : 𝒰₀+U covers [ a , x₀ ]
            covSup .fst {x = x} x∈[a,x₀] = case-split (<≤-total y x)
              where
              case-split : _ → _
              case-split (inl x>y) = ∪-helper (inr (ℬx₀r⊆U x∈ℬx₀r))
                where
                x∈ℬx₀r : x ∈ ℬ x₀ r
                x∈ℬx₀r = Inhab→∈ℬ (absInBetween<≤ r>0 (<-trans x₀-r<y x>y) (∈→Inhab𝐈-R x∈[a,x₀]))
              case-split (inr x≤y) = ∪-helper (inl (cov .fst x∈[a,y]))
                where
                x∈[a,y] : x ∈ [ a , y ]
                x∈[a,y] = Inhab→∈𝐈 (∈→Inhab𝐈-L x∈[a,x₀]) x≤y
            covSup .snd = ⊆-trans {A = 𝒰₀+U} 𝒰₀+U∈𝒰 (𝒰cov𝐈 .snd)

            x₀∈cov : x₀ ∈ cov-sub
            x₀∈cov = Inhab→∈ cov-prop (x₀∈𝐈 , ∣ 𝒰₀+U , 𝒰₀+U∈𝒰 , fin𝒰₀+U , covSup ∣)

            module _ (x₀<b : x₀ < b) where

              ε-triple = min2 {y = b - x₀} r>0 (>→Diff>0 x₀<b)

              ε = ε-triple .fst
              ε>0 = ε-triple .snd .fst
              ε<r = ε-triple .snd .snd .fst
              ε<b-x₀ = ε-triple .snd .snd .snd

              instance
                a≤x₀+ε : a ≤ x₀ + ε
                a≤x₀+ε = inl (≤<-trans x₀≥a (+-rPos→> ε>0))

              x₀+ε∈𝐈 : (x₀ + ε) ∈ [ a , b ]
              x₀+ε∈𝐈 = Inhab→∈𝐈 a≤x₀+ε (inl (-MoveRToL<' ε<b-x₀))

              covMore : 𝒰₀+U covers [ a , x₀ + ε ]
              covMore .fst {x = x} x∈[a,x₀+ε] = case-split (<≤-total y x)
                where
                case-split : _ → _
                case-split (inl x>y) = ∪-helper (inr (ℬx₀r⊆U x∈ℬx₀r))
                  where
                  x∈ℬx₀r : x ∈ ℬ x₀ r
                  x∈ℬx₀r = Inhab→∈ℬ (absInOpenInterval r>0 (<-trans x₀-r<y x>y)
                    (≤<-trans (∈→Inhab𝐈-R x∈[a,x₀+ε]) (+-lPres< ε<r)))
                case-split (inr x≤y) = ∪-helper (inl (cov .fst x∈[a,y]))
                  where
                  x∈[a,y] : x ∈ [ a , y ]
                  x∈[a,y] = Inhab→∈𝐈 (∈→Inhab𝐈-L x∈[a,x₀+ε]) x≤y
              covMore .snd = ⊆-trans {A = 𝒰₀+U} 𝒰₀+U∈𝒰 (𝒰cov𝐈 .snd)

              no-way : ⊥
              no-way = <≤-asym (+-rPos→> ε>0) (cov-sup .bound _ x₀+ε∈cov)
                where
                x₀+ε∈cov : (x₀ + ε) ∈ cov-sub
                x₀+ε∈cov = Inhab→∈ cov-prop (x₀+ε∈𝐈 , ∣ 𝒰₀+U , 𝒰₀+U∈𝒰 , fin𝒰₀+U , covMore ∣)

            x₀∈cov×¬x₀<b' : (x₀ ∈ cov-sub) × (¬ x₀ < b)
            x₀∈cov×¬x₀<b' = x₀∈cov , no-way

        ∃ℬ : ∥ Σ[ U ∈ ℙ ℝ ] Σ[ r ∈ ℝ ] Σ[ r>0 ∈ r > 0 ] (U ∈ 𝒰) × (ℬ x₀ r ⦃ r>0 ⦄ ⊆ U) ∥
        ∃ℬ = Prop.rec squash
          (λ (U , x₀∈U , U∈𝒰) → Prop.map
          (λ (r , r>0 , ℬxr⊆U) → U , r , r>0 , U∈𝒰 , (λ p → ℬxr⊆U p))
          (∈→Inhab𝓂 (𝒰cov𝐈 .snd U∈𝒰) x₀ x₀∈U))
          (∈cover x₀∈𝐈 𝒰cov𝐈)

        isProp×' : isProp ((x₀ ∈ cov-sub) × (¬ x₀ < b))
        isProp×' = isProp× (isProp∈ cov-sub) (isProp¬ _)

        x₀∈cov×¬x₀<b : (x₀ ∈ cov-sub) × (¬ x₀ < b)
        x₀∈cov×¬x₀<b = Prop.rec isProp×'
          (λ (U , r , r>0 , U∈𝒰 , ℬxr⊆U) → Prop.rec isProp×'
          (λ (y , x₀-r<y , y∈sub) → Prop.rec isProp×'
          (λ (𝒰₀ , 𝒰₀⊆𝒰 , fin𝒰₀ , cov) →
            x₀∈cov×¬x₀<b'
              U r ⦃ r>0 ⦄ U∈𝒰 ℬxr⊆U
              y x₀-r<y y∈sub
              𝒰₀ 𝒰₀⊆𝒰 fin𝒰₀ cov)
          (∈→Inhab cov-prop y∈sub .snd))
          (<sup→∃∈ (x₀ - r) cov-sup (-rPos→< r>0))) ∃ℬ

        x₀≡b : x₀ ≡ b
        x₀≡b = ≤+¬<→≡ x₀≤b (x₀∈cov×¬x₀<b .snd)

        cov[a,b]' : cov-prop b .fst
        cov[a,b]' = ∈→Inhab cov-prop (subst (_∈ cov-sub) x₀≡b (x₀∈cov×¬x₀<b .fst))

        cov[a,b] : ∥ Σ[ 𝒰₀ ∈ ℙ (ℙ ℝ) ] 𝒰₀ ⊆ 𝒰 × isFinSub 𝒰₀ × 𝒰₀ covers [ a , b ] ∥
        cov[a,b] = cov[a,b]' .snd


    -- Closed interval is closed.

    isClosedInterval : isClosedSub [ a , b ]
    isClosedInterval = isCompactSub→isClosedSub isHausdorffℝ isCompactInterval


  {-

    Bounded Subset

  -}


  -- Two usual formulations of boundedness, and they are equivalent.

  isBoundedSub : ℙ ℝ → Type
  isBoundedSub A = ∥ Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] (a ≤ b) × ((x : ℝ) → x ∈ A → (a ≤ x) × (x ≤ b)) ∥

  isBoundedByInterval : ℙ ℝ → Type
  isBoundedByInterval A = ∥ Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] Σ[ a≤b ∈ a ≤ b ] A ⊆ [ a , b ] ⦃ a≤b ⦄ ∥

  isBoundedSub→isBoundedByInterval : {A : ℙ ℝ} → isBoundedSub A → isBoundedByInterval A
  isBoundedSub→isBoundedByInterval =
    Prop.map (λ (a , b , a≤b , h) →
      a , b , a≤b , λ {x} x∈A → Inhab→∈𝐈 ⦃ a≤b ⦄ (h x x∈A .fst) (h x x∈A .snd))

  isBoundedByInterval→isBoundedSub : {A : ℙ ℝ} → isBoundedByInterval A → isBoundedSub A
  isBoundedByInterval→isBoundedSub =
    Prop.map (λ (a , b , a≤b , A⊆𝐈) →
      a , b , a≤b , λ x x∈A → ∈→Inhab𝐈-L ⦃ a≤b ⦄ (A⊆𝐈 x∈A) , ∈→Inhab𝐈-R ⦃ a≤b ⦄ (A⊆𝐈 x∈A))


  {-

    Heine-Borel Theorem

  -}

  -- A bounded and closed subset of ℝ is compact under the canonical topology.

  isBoundedClosedSub→isCompactSub : {A : ℙ ℝ} → isBoundedSub A → isClosedSub A → isCompactSub A
  isBoundedClosedSub→isCompactSub {A = A} bA cA =
    Prop.rec isPropIsCompactSub
    (λ (a , b , a≤b , A⊆𝐈) →
      isClosedInCompact→isCompact A⊆𝐈 cA ( isCompactInterval a b ⦃ a≤b ⦄))
    (isBoundedSub→isBoundedByInterval bA)
