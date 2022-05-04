{-

Totally Ordered Field

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Classical.Algebra.Field
open import Classical.Algebra.OrderedRing

private
  variable
    ℓ ℓ' : Level


OrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedField ℓ ℓ' = Σ[ 𝒦 ∈ OrderedRing ℓ ℓ' ] isField (𝒦 .fst)
