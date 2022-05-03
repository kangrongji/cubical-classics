{-

A Technical Lemma about Archimedean-ness

-}
{-# OPTIONS --allow-unsolved-meta --experimental-lossy-unification #-}
module Classical.Analysis.Real.Base.Archimedes where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (q r : 𝓡 .fst) → q ≡ r + (q - r)
    helper1 = solve 𝓡

    helper2 : (q r : 𝓡 .fst) → q ≡ (q + r) - r
    helper2 = solve 𝓡

    helper3 : (p q r : 𝓡 .fst) → q · (p · r) ≡ p · (q · r)
    helper3 = solve 𝓡

    helper4 : (q r : 𝓡 .fst) → r + (r · (q - 1r)) ≡ r · q
    helper4 = solve 𝓡


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.Rationals.QuoQ using (ℚ)
open import Cubical.Relation.Nullary

open import Classical.Preliminary.QuoQ
open import Classical.Algebra.Field
open import Classical.Algebra.OrderedRing
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Analysis.Real.Base.DedekindCut

open Helpers (ℚOrder .fst)


module Archimedes (decide : LEM) where

  open Powerset decide

  open Basics   decide
  open DedekindCut

  open FieldStr       ℚField
  open OrderedRingStr ℚOrder


  archimedes' : (a : ℝ)(ε : ℚ)(ε>0 : ε > 0)
    → (p : ℚ)  → Σ[ s ∈ ℚ ] ((q : ℚ) → q ∈ a .upper → s < q) × (p < s)
    → Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ] ((q : ℚ) → q ∈ a .upper → s < q) × (p < r) × (r < s) × (r + ε) ∈ a .upper
  archimedes' = {!!}

  archimedes : (a : ℝ)(ε : ℚ)(ε>0 : ε > 0)
    → ∥ Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ] ((q : ℚ) → q ∈ a .upper → s < q) × (r < s) × (r + ε) ∈ a .upper ∥
  archimedes = {!!}
