{-

Axiom of Choice

-}
{-# OPTIONS --safe #-}
module Classics.Axioms.Choice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as Prop

private
  variable
    ℓ ℓ' : Level

AC : Typeω
AC = {ℓ ℓ' : Level}{X : Type ℓ}{Y : X → Type ℓ'}
  → isSet X
  → ((x : X) → isSet (Y x))
  → ((x : X) → ∥ Y x ∥) → ∥ ((x : X) → Y x) ∥

AC2 : Typeω
AC2 = {ℓ ℓ' ℓ'' : Level}{X : Type ℓ}{Y : X → Type ℓ'}{Z : (x : X) → Y x → Type ℓ''}
  → isSet X
  → ((x : X) → isSet (Y x))
  → ((x : X) → (y : Y x) → isSet (Z x y))
  → ((x : X) → (y : Y x) → ∥ Z x y ∥) → ∥ ((x : X) → (y : Y x) → Z x y) ∥

module AxiomOfChoices (choice : AC) where

  choice2 : AC2
  choice2 isSetX isSetY isSetZ f =
    choice isSetX (λ x → isSetΠ (isSetZ x)) (λ x → choice (isSetY x) (isSetZ x) (f x))
