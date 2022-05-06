{-# OPTIONS --safe #-}
module Classical.Algebra.Field.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level


module _ (𝓡 : CommRing ℓ) where

  open CommRingStr (𝓡 .snd)
  open Units        𝓡

  private
    R = 𝓡 .fst

  isField : Type ℓ
  isField = (x : R) → ¬ x ≡ 0r → Σ[ y ∈ R ] x · y  ≡ 1r

  isPropIsField : isProp isField
  isPropIsField = isPropΠ2 (λ x _ → inverseUniqueness x)


Field : (ℓ : Level) → Type (ℓ-suc ℓ)
Field ℓ = Σ[ 𝓡 ∈ CommRing ℓ ] isField 𝓡
