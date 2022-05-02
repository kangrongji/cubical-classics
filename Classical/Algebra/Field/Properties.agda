{-# OPTIONS --safe #-}
module Classical.Algebra.Field.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Nullary

open import Classical.Algebra.Field.Base

private
  variable
    ℓ : Level


module FieldStr (𝒦 : Field ℓ) where

  private
    K = 𝒦 .fst .fst
    isFieldK = 𝒦 .snd

  private
    variable
      x : K

  open CommRingStr (𝒦 .fst .snd) public
  open Units       (𝒦 .fst)      public

  inv : ¬ x ≡ 0r → K
  inv x≢0 = isFieldK _ x≢0 .fst

  ·-rInv : (x≢0 : ¬ x ≡ 0r) → x · inv x≢0 ≡ 1r
  ·-rInv x≢0 = isFieldK _ x≢0 .snd

  ·-lInv : (x≢0 : ¬ x ≡ 0r) → inv x≢0 · x ≡ 1r
  ·-lInv x≢0 = ·Comm _ _ ∙ ·-rInv x≢0
