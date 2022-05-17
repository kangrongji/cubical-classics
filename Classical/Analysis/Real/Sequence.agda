{-

Cauchy Sequence of Real Numbers

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order
  using () renaming (_>_ to _>ℕ_ ; _<_ to _<ℕ_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms.ExcludedMiddle
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Analysis.Real.Base


module Cauchy (decide : LEM) where

  open Real decide
  open OrderedFieldStr (ℝCompleteOrderedField .fst)

  test : (x : ℝ) → x · 0r ≡ 0r
  test x = 0RightAnnihilates x

  {-

    Convergence and Limit of Real Number Sequence

  -}

  isConvergentTo : (ℕ → ℝ) → ℝ → Type
  isConvergentTo seq x = (ε : ℝ) → ε > 0 → ∥ Σ[ N ∈ ℕ ] ((n : ℕ) → n >ℕ N → abs (x - seq n) < ε) ∥

  record Limit (seq : ℕ → ℝ) : Type where
    field
      lim : ℝ
      conv : isConvergentTo seq lim


  isCauchy : (ℕ → ℝ) → Type
  isCauchy seq = (ε : ℝ) → ε > 0 → ∥ Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → abs (seq m - seq n) < ε) ∥

  record CauchySequence : Type where
    field
      seq : ℕ → ℝ
      accum : isCauchy seq


  -- Real Number is Cauchy Complete

  converge : (seq : ℕ → ℝ) → isCauchy seq → Limit seq
  converge = {!!}


  record Subsequence (seq : ℕ → ℝ) : Type where
    field
      incl : ℕ → ℕ
      incrs : (n : ℕ) → incl (suc n) >ℕ incl n

  open Subsequence

  subseq : {seq : ℕ → ℝ} → Subsequence seq → ℕ → ℝ
  subseq {seq = seq} sub n = seq (sub .incl n)


  -- The Bolzano-Weierstrass Theorem

  isBoundedSequence : (ℕ → ℝ) → Type
  isBoundedSequence seq = ∥ Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] ((n : ℕ) → (a ≤ seq n) × (seq n ≤ b)) ∥

  bolwei : (seq : ℕ → ℝ) → isBoundedSequence seq → Σ[ sub ∈ Subsequence seq ] Limit (subseq sub)
  bolwei = {!!}
