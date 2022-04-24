{-

The Real Number

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Analysis.Real where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.Rationals.QuoQ
  renaming (_∼_ to _∼ℚ_)

open import Classical.Preliminary.Rational

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset


module Real (decide : LEM) where

  open Powerset decide

  record DedekindCut : Type where
    field
      upper : ℙ ℚ
      lower : ℙ ℚ
      upper-inhab : ∥ Σ[ q ∈ ℚ ] q ∈ upper ∥
      lower-inhab : ∥ Σ[ q ∈ ℚ ] q ∈ lower ∥
      upper-closed : {r : ℚ}(q : ℚ) → q ∈ upper → q < r → r ∈ upper
      lower-closed : {r : ℚ}(q : ℚ) → q ∈ lower → r < q → r ∈ lower
      upper-round : (q : ℚ) → q ∈ upper → Σ[ r ∈ ℚ ] (r < q) × (r ∈ upper)
      lower-round : (q : ℚ) → q ∈ lower → Σ[ r ∈ ℚ ] (q < r) × (r ∈ lower)
      order : (p q : ℚ) → p ∈ lower → q ∈ upper → p < q

  open DedekindCut

  ℝ : Type
  ℝ = DedekindCut

  _+ℝ_ : ℝ → ℝ → ℝ
  (a +ℝ b) .upper = specify (λ r → ∥ Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ] p ∈ a .upper × q ∈ b .upper × (r ≡ p + q) ∥ , squash)

