{-# OPTIONS --safe #-}
module Classical.Axioms where

open import Cubical.Foundations.Prelude public

open import Classical.Axioms.Choice public
open import Classical.Axioms.ExcludedMiddle public


record Oracle : Typeω where
  field
    decide : LEM
