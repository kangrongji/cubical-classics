{-

The Real Number

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Analysis.Real.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.Rationals.QuoQ

open import Classical.Preliminary.Rational
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset


module Real (decide : LEM) where

  open Powerset decide

  record DedekindCut : Type where
    field
      lower : ℙ ℚ
      lower-inhab : ∥ Σ[ q ∈ ℚ ] q ∈ lower ∥
      lower-close : (r : ℚ)(q : ℚ) → q ∈ lower → r < q → r ∈ lower
      lower-round : (q : ℚ) → q ∈ lower → ∥ Σ[ r ∈ ℚ ] (q < r) × (r ∈ lower) ∥

      upper : ℙ ℚ
      upper-inhab : ∥ Σ[ q ∈ ℚ ] q ∈ upper ∥
      upper-close : (r : ℚ)(q : ℚ) → q ∈ upper → q < r → r ∈ upper
      upper-round : (q : ℚ) → q ∈ upper → ∥ Σ[ r ∈ ℚ ] (r < q) × (r ∈ upper) ∥

      order : (p q : ℚ) → p ∈ lower → q ∈ upper → p < q

  open DedekindCut

  ℝ : Type
  ℝ = DedekindCut

  path-ℝ : (a b : DedekindCut) → a .lower ≡ b .lower → a .upper ≡ b .upper → a ≡ b
  path-ℝ a b lower-path upper-path i .lower = lower-path i
  path-ℝ a b lower-path upper-path i .lower-inhab =
    isProp→PathP (λ i → squash {A = Σ[ q ∈ ℚ ] q ∈ lower-path i}) (a .lower-inhab) (b .lower-inhab) i
  path-ℝ a b lower-path upper-path i .lower-round =
    isProp→PathP (λ i → isPropΠ2 {B = λ q → q ∈ lower-path i}
      (λ q _ → squash {A = Σ[ r ∈ ℚ ] (q < r) × (r ∈ lower-path i)}))
    (a .lower-round) (b .lower-round) i
  path-ℝ a b lower-path upper-path i .lower-close =
    isProp→PathP (λ i → isPropΠ4 {C = λ _ q → q ∈ lower-path i} (λ _ _ _ _ → isProp∈ (lower-path i)))
    (a .lower-close) (b .lower-close) i
  path-ℝ a b lower-path upper-path i .upper = upper-path i
  path-ℝ a b lower-path upper-path i .upper-inhab =
    isProp→PathP (λ i → squash {A = Σ[ q ∈ ℚ ] q ∈ upper-path i}) (a .upper-inhab) (b .upper-inhab) i
  path-ℝ a b lower-path upper-path i .upper-close =
    isProp→PathP (λ i → isPropΠ4 {C = λ _ q → q ∈ upper-path i} (λ _ _ _ _ → isProp∈ (upper-path i)))
    (a .upper-close) (b .upper-close) i
  path-ℝ a b lower-path upper-path i .upper-round =
    isProp→PathP (λ i → isPropΠ2 {B = λ q → q ∈ upper-path i}
      (λ q _ → squash {A = Σ[ r ∈ ℚ ] (r < q) × (r ∈ upper-path i)}))
    (a .upper-round) (b .upper-round) i
  path-ℝ a b lower-path upper-path i .order =
    isProp→PathP (λ i → isPropΠ4 {C = λ p _ → p ∈ lower-path i} {D = λ _ q _ → q ∈ upper-path i}
      (λ _ _ _ _ → isProp<)) (a .order) (b .order) i

  isSetℝ : isSet ℝ
  isSetℝ a b p q i j =
    hcomp (λ k → λ
      { (i = i0) → path-ℝ (lift-square i0 j) (p j) refl refl k
      ; (i = i1) → path-ℝ (lift-square i1 j) (q j) refl refl k
      ; (j = i0) → path-ℝ a a refl refl k
      ; (j = i1) → path-ℝ b b refl refl k })
    (lift-square i j)
    where
    lift-square : (i j : I) → ℝ
    lift-square i j = path-ℝ a b
      (isSet→SquareP (λ _ _ → isSetℙ {X = ℚ}) (cong lower p) (cong lower q) refl refl i)
      (isSet→SquareP (λ _ _ → isSetℙ {X = ℚ}) (cong upper p) (cong upper q) refl refl i) j

  ℚ→ℝ : ℚ → ℝ
  ℚ→ℝ q .lower = specify (λ r → (r < q) , isProp<)


  ℚ→ℝ q .upper = specify (λ r → (r > q) , isProp<)
{-
-- Natural number and negative integer literals for ℝ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℚ : HasFromNat ℚ
  fromNatℚ = record { Constraint = λ _ → Unit ; fromNat = λ n → [ pos n , 1 ] }

instance
  fromNegℚ : HasFromNeg ℚ
  fromNegℚ = record { Constraint = λ _ → Unit ; fromNeg = λ n → [ neg n , 1 ] }
-}