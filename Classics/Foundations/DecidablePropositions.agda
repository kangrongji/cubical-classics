{-# OPTIONS --safe #-}
module Classics.Foundations.DecidablePropositions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Cubical.Relation.Nullary


private
  variable
    ℓ : Level

DecProp : (ℓ : Level) → Type (ℓ-suc ℓ)
DecProp ℓ = Σ[ P ∈ hProp ℓ ] Dec (P .fst)

isPropIsDecProp : (P : hProp ℓ) → isProp (Dec (P .fst))
isPropIsDecProp P = isPropDec (P .snd)

isSetDecProp : isSet (DecProp ℓ)
isSetDecProp = isOfHLevelΣ 2 isSetHProp (λ P → isProp→isSet (isPropIsDecProp P))

Bool→DecProp : Bool → DecProp ℓ
Bool→DecProp true .fst .fst = {!!}
