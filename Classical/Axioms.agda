{-# OPTIONS --safe #-}
module Classical.Axioms where

open import Cubical.Foundations.Prelude public

open import Classical.Axioms.Choice public
open import Classical.Axioms.ExcludedMiddle public


-- We record up axioms to make use of Agda's instance argument,
-- so we don't need to write them explicitly everywhere.

record Oracle : Typeω where
  field
    decide : LEM
