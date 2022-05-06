{-

Dedekind Completeness of Ordered Field

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Completeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset
open import Classical.Algebra.OrderedField

private
  variable
    ℓ ℓ' : Level


module CompleteOrderedField (decide : LEM) where


  module _ (𝒦 : OrderedField ℓ ℓ') where

    private
      K = 𝒦 .fst .fst .fst

      variable
        p q : K

    open Powerset   decide
    open OrderedFieldStr 𝒦


    record Supremum (A : ℙ K) : Type (ℓ-max ℓ ℓ') where
      field
        sup : K
        bound : (r : K) → r ∈ A → r ≤ sup
        least : (b : K) → ((r : K) → r ∈ A → r ≤ b) → b ≥ sup

    open Supremum

    isPropSupremum : (A : ℙ K) → isProp (Supremum A)
    isPropSupremum A s t i .sup = ≤-asym (s .least _ (t .bound)) (t .least _ (s .bound)) i
    isPropSupremum A s t i .bound =
      isProp→PathP (λ i → isPropΠ2 (λ r _ → isProp≤ {x = r} {y = isPropSupremum A s t i .sup})) (s .bound) (t .bound) i
    isPropSupremum A s t i .least =
      isProp→PathP (λ i → isPropΠ2 (λ b _ → isProp≤ {x = isPropSupremum A s t i .sup} {y = b})) (s .least) (t .least) i


    -- Boundedness of subsets

    isUpperBounded : ℙ K → Type (ℓ-max ℓ ℓ')
    isUpperBounded A = ∥ Σ[ b ∈ K ] ((r : K) → r ∈ A → r ≤ b) ∥


    -- The Supremum Principle/Dedekind Completeness of Real Numbers

    isComplete : Type (ℓ-max ℓ ℓ')
    isComplete = {A : ℙ K} → isInhabited A → isUpperBounded A → Supremum A


  CompleteOrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  CompleteOrderedField ℓ ℓ' = Σ[ 𝒦 ∈ OrderedField ℓ ℓ' ] isComplete 𝒦


  module CompleteOrderedFieldStr (𝒦 : CompleteOrderedField ℓ ℓ') where

    -- TODO: Basic corollaries of completeness.
