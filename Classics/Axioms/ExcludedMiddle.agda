{-

Law of Excluded Middle

-}
{-# OPTIONS --safe #-}
module Classics.Axioms.ExcludedMiddle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level


-- LEM for Law of Excluded Middle and DNE for Double Negation Elimination
-- The "per universe" version.

LEMOfLevel : (ℓ : Level) → Type (ℓ-suc ℓ)
LEMOfLevel ℓ = {P : Type ℓ} → isProp P → Dec P

DNEOfLevel : (ℓ : Level) → Type (ℓ-suc ℓ)
DNEOfLevel ℓ = {P : Type ℓ} → isProp P → ¬ ¬ P → P

isPropLEMOfLevel : isProp (LEMOfLevel ℓ)
isPropLEMOfLevel = isPropImplicitΠ (λ _ → isPropΠ isPropDec)

isPropDNEOfLevel : isProp (DNEOfLevel ℓ)
isPropDNEOfLevel = isPropImplicitΠ (λ _ → isPropΠ2 (λ p _ → p))

-- Equivalence between these two axioms

LEMOfLevel→DNEOfLevel : LEMOfLevel ℓ → DNEOfLevel ℓ
LEMOfLevel→DNEOfLevel decide isPropP ¬¬p =
  case decide isPropP of λ
    { (yes p) → p
    ; (no ¬p) → Empty.rec (¬¬p ¬p) }

DNEOfLevel→LEMOfLevel : DNEOfLevel ℓ → LEMOfLevel ℓ
DNEOfLevel→LEMOfLevel elim¬¬ {P = P} isPropP = elim¬¬ (isPropDec isPropP) ¬¬dec
  where
  ¬¬dec : ¬ ¬ Dec P
  ¬¬dec ¬dec = ¬dec (yes (elim¬¬ isPropP λ ¬p → ¬dec (no ¬p)))

-- The universal polymorphic version

LEM : Typeω
LEM = {ℓ : Level} → LEMOfLevel ℓ

DNE : Typeω
DNE = {ℓ : Level} → DNEOfLevel ℓ

LEM→DNE : LEM → DNE
LEM→DNE p = LEMOfLevel→DNEOfLevel p

DNE→LEM : DNE → LEM
DNE→LEM p = DNEOfLevel→LEMOfLevel p
