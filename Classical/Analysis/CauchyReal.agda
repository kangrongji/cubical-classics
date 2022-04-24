{-

The Real Number

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Analysis.CauchyReal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
  renaming (_<_ to _<ℕ_)

open import Cubical.HITs.Rationals.QuoQ
  renaming (_∼_ to _∼ℚ_)

open import Cubical.HITs.SetQuotients as SetQuot
  using (_/_ ; [_] ; eq/ ; discreteSetQuotients)

open import Classical.Preliminary.Rational
  renaming (_<_ to _<ℚ_ ; _>_ to _>ℚ_)


_>ℕ_ : ℕ → ℕ → Type
m >ℕ n = m <ℕ n

------------------------------------

record CauchySequenceℚ : Type where
  field
    seq : ℕ → ℚ
    cauchy : (ε : ℚ) → ε >ℚ 0 → Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → ∣ seq m - seq n ∣ <ℚ ε)

open CauchySequenceℚ

_∼_ : CauchySequenceℚ → CauchySequenceℚ → Type
a ∼ b = (ε : ℚ) → ε >ℚ 0 → Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → ∣ a .seq m - b .seq n ∣ <ℚ ε)

ℝ : Type
ℝ = CauchySequenceℚ / _∼_

--_<ᶜ_ : CauchySequenceℚ → CauchySequenceℚ → Type
--a <ᶜ b : 

_<_ : ℝ → ℝ → ℝ
_<_ = {!!}

_>_ : ℝ → ℝ → ℝ
r > s = s < r

{-
record CauchySequence : Type where
  field
    seq : ℕ → ℝ
    cauchy : (ε : ℝ) → _ → Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → ∣ seq m - seq n ∣ < ε)
-}
