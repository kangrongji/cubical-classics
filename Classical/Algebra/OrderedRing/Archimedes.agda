{-

  Archimedean-ness of Ordered Ring

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedRing.Archimedes where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Algebra.CommRing

open import Classical.Algebra.OrderedRing

private
  variable
    ℓ ℓ' : Level


module _ (𝓡 : OrderedRing ℓ ℓ') where

  private
    R = 𝓡 .fst .fst

  open CommRingStr   (𝓡 .fst .snd)
  open OrderedRingStr 𝓡

  -- Although we only need the following un-truncated version,
  -- It is better to use an truncated version.
  isArchimedean : Type (ℓ-max ℓ ℓ')
  isArchimedean = (q ε : R) → ε > 0r → Σ[ n ∈ ℕ ] n ⋆ ε > q
