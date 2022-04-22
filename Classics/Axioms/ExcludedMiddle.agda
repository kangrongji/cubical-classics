{-

Law of Excluded Middle

-}
{-# OPTIONS --safe #-}
module Classics.Axioms.ExcludedMiddle where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

LEMOfLevel : (ℓ : Level) → Type (ℓ-suc ℓ)
LEMOfLevel ℓ = {P : Type ℓ} → isProp P → Dec P

LEM : Typeω
LEM = {ℓ : Level} → LEMOfLevel ℓ
