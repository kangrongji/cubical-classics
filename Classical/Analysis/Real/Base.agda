{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Base where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.Rationals.QuoQ using (ℚ)
open import Classical.Analysis.Real.Base.DedekindCut
open import Classical.Analysis.Real.Base.Algebra
open import Classical.Axioms.ExcludedMiddle

module Real (decide : LEM) where

  open Basics  decide
    renaming (ℝ to ℝDedekind ; ℚ→ℝ to ℚ→ℝDedekind)
  open Algebra decide


  abstract
