{-# OPTIONS --safe #-}
module Classical.Preliminary.QuoQ.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.MoreInts.QuoInt
open import Cubical.HITs.Rationals.QuoQ


-- Inclusion from Natural Numbers

ℕ→ℚPos : ℕ → ℚ
ℕ→ℚPos n = [ pos n / 1 ]

ℕ→ℚNeg : ℕ → ℚ
ℕ→ℚNeg n = [ neg n / 1 ]
