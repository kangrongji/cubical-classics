{-

Some useful logical identity

-}
{-# OPTIONS --safe #-}
module Classics.Preliminary.Logic where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ
    Y : Type ℓ'

¬map : (X → Y) → ¬ Y → ¬ X
¬map f ¬y x = ¬y (f x)

→¬¬ : X → ¬ ¬ X
→¬¬ x ¬x = ¬x x
