{-

Dedekind Completion is Complete

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.OrderedField.DedekindCut.Completeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad

open import Classical.Axioms
open import Classical.Foundations.Powerset

open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Extremum
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Algebra.OrderedField.DedekindCut.Base
open import Classical.Algebra.OrderedField.DedekindCut.Order
open import Classical.Algebra.OrderedField.DedekindCut.Multiplication

private
  variable
    ℓ ℓ' : Level


module CompletenessOfCuts ⦃ 🤖 : Oracle ⦄
  (𝒦 : OrderedField ℓ ℓ')(archimedes : isArchimedean (𝒦 . fst))
  where

  private
    K = 𝒦 .fst .fst .fst

  open OrderedFieldStr 𝒦
  open Basics   𝒦
  open Order    𝒦 archimedes
  open Multiplication 𝒦 archimedes
  open DedekindCut

  open CompleteOrderedField
  open Extremum 𝕂OrderedField
  open Supremum

  open OrderedFieldStr 𝕂OrderedField using ()
    renaming (_<_ to _<𝕂'_ ; _>_ to _>𝕂'_ ; _≤_ to _≤𝕂'_ ; _≥_ to _≥𝕂'_)


  module _
    (A : ℙ 𝕂)(a₀ : 𝕂)(a₀∈A : a₀ ∈ A)
    (s : K)(bound : (x : 𝕂) → x ∈ A → s ∈ x .upper) where

    sup-upper : K → hProp (ℓ-max ℓ ℓ')
    sup-upper a = ∥ Σ[ q ∈ K ] ((x : 𝕂) → x ∈ A → q ∈ x .upper) × (q < a) ∥₁ , squash₁

    sup𝕂 : 𝕂
    sup𝕂 .upper = specify sup-upper
    sup𝕂 .upper-inhab = ∣ s + 1r , Inhab→∈ sup-upper ∣ s , bound , q+1>q ∣₁ ∣₁
    sup𝕂 .upper-close r q q∈sup q<r =
      proof _ , isProp∈ (sup𝕂 .upper) by do
      (p , p∈x∈A , p<q) ← ∈→Inhab sup-upper q∈sup
      return (Inhab→∈ sup-upper ∣ p , p∈x∈A , <-trans p<q q<r ∣₁)

    sup𝕂 .upper-round q q∈sup = do
      (p , p∈x∈A , p<q) ← ∈→Inhab sup-upper q∈sup
      return (
        middle p q , middle<r p<q ,
        Inhab→∈ sup-upper ∣ p , p∈x∈A , middle>l p<q ∣₁)

    sup𝕂 .lower-inhab = do
      (p , p<r∈upper) ← a₀ .lower-inhab
      return (p , λ q q∈sup →
        proof _ , isProp< by do
        (r , r∈x∈A , r<q) ← ∈→Inhab sup-upper q∈sup
        return (<-trans (p<r∈upper r (r∈x∈A a₀ a₀∈A)) r<q))

    boundSup𝕂 : (x : 𝕂) → x ∈ A → x ≤𝕂 sup𝕂
    boundSup𝕂 x x∈A {x = q} q∈sup =
      proof _ , isProp∈ (x .upper) by do
      (p , p∈x∈A , p<q) ← ∈→Inhab sup-upper q∈sup
      return (x .upper-close q p (p∈x∈A x x∈A) p<q)

    leastSup𝕂 : (y : 𝕂) → ((x : 𝕂) → x ∈ A → x ≤𝕂 y) → y ≥𝕂 sup𝕂
    leastSup𝕂 y x∈A→x≤y {x = q} q∈y =
      proof _ , isProp∈ (sup𝕂 .upper) by do
      (r , r<q , r∈y) ← y .upper-round q q∈y
      return (Inhab→∈ sup-upper ∣ r , (λ x x∈A → x∈A→x≤y x x∈A r∈y) , r<q ∣₁)

    boundSup𝕂' : (x : 𝕂) → x ∈ A → x ≤𝕂' sup𝕂
    boundSup𝕂' x h = ≤𝕂→≤𝕂' _ _ (boundSup𝕂 x h)

    leastSup𝕂' : (y : 𝕂) → ((x : 𝕂) → x ∈ A → x ≤𝕂' y) → y ≥𝕂' sup𝕂
    leastSup𝕂' y h = ≤𝕂→≤𝕂' _ _ (leastSup𝕂 y (λ x k → ≤𝕂'→≤𝕂 _ _ (h x k)))


  private
    findBound : (A : ℙ 𝕂)
      → (b : 𝕂)(bound : (x : 𝕂) → x ∈ A → x ≤𝕂' b)
      → ∥ Σ[ s ∈ K ] ((x : 𝕂) → x ∈ A → s ∈ x .upper) ∥₁
    findBound A b bound = do
      (s , s∈b) ← b .upper-inhab
      return (s , λ x x∈A → ≤𝕂'→≤𝕂 _ _ (bound x x∈A) s∈b)


  {-

    Complete Ordered Field Instance

  -}

  isComplete𝕂 : isComplete 𝕂OrderedField
  isComplete𝕂 {A = A} =
    Prop.rec2 (isPropSupremum A)
    (λ (a₀ , a₀∈A) (b , bound) →
      proof _ , isPropSupremum A by do
      (s , s∈x∈A) ← findBound A b bound
      return record
        { sup = sup𝕂 A a₀ a₀∈A s s∈x∈A
        ; bound = boundSup𝕂' A a₀ a₀∈A s s∈x∈A
        ; least = leastSup𝕂' A a₀ a₀∈A s s∈x∈A })

  𝕂CompleteOrderedField : CompleteOrderedField (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  𝕂CompleteOrderedField = 𝕂OrderedField , isComplete𝕂
