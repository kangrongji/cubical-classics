{-

Propositional Resizing

-}
{-# OPTIONS --safe #-}
module Classics.Axioms.Resizing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

private
  variable
    ℓ ℓ' : Level

liftProp : (ℓ' : Level) → hProp ℓ → hProp (ℓ-max ℓ ℓ')
liftProp ℓ' P .fst = Lift {j = ℓ'} (P .fst)
liftProp ℓ' P .snd = isOfHLevelLift 1 (P .snd)

Resizing : Typeω
Resizing = {ℓ ℓ' : Level} → isEquiv (liftProp {ℓ = ℓ} ℓ')


record DropProp (P : hProp ℓ) : Type (ℓ-suc ℓ) where
  field
    lower : hProp ℓ-zero
    dropEquiv : P .fst ≃ lower .fst

open DropProp

Drop : Typeω
Drop = {ℓ : Level} → (P : hProp ℓ) → DropProp P

open isEquiv

Resizing→Drop : Resizing → Drop
Resizing→Drop resizing P .lower = resizing .equiv-proof P .fst .fst
