{-

Impredicativity

-}
{-# OPTIONS --safe #-}
module Classics.Foundations.Impredicativity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Relation.Nullary

open import Classics.Axioms.ExcludedMiddle

private
  variable
    ℓ : Level
    X : Type ℓ


-- Renaming to emphasize Prop is a subobject classifier in classical world.

Prop : Type ℓ-zero
Prop = Bool

isSetProp : isSet Prop
isSetProp = isSetBool

type : Prop → Type ℓ-zero
type = Bool→Type

bool : Dec X → Prop
bool = Dec→Bool


module Impredicativity (decide : LEM) where
  -- TODO:
  -- Show that Prop is subobject classifier
  -- and the axiom of Propositional Resizing holds
  -- under the assumption of LEM.
