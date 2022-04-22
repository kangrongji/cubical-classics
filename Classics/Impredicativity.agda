{-# OPTIONS --safe #-}
module Classics.Impredicativity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Cubical.Relation.Nullary

open import Classics.Axioms.ExcludedMiddle

private
  variable
    ℓ : Level

DecProp : (ℓ : Level) → Type (ℓ-suc ℓ)
DecProp ℓ = Σ[ P ∈ hProp ℓ ] Dec (P .fst)

isPropIsDecProp : (P : hProp ℓ) → isProp (Dec (P .fst))
isPropIsDecProp P = isPropDec (P .snd)

isSetDecProp : isSet (DecProp ℓ)
isSetDecProp = isOfHLevelΣ 2 isSetHProp (λ P → isProp→isSet (isPropIsDecProp P))


module Impredicativity (lem : LEM)
  where

  -- By LEM, we have proposition classifier
  Prop = Bool
  isSetProp = isSetBool

  hProp→DecProp : hProp ℓ → DecProp ℓ
  hProp→DecProp P = P , lem (P .snd)

  DecProp→hProp : DecProp ℓ → hProp ℓ
  DecProp→hProp = fst

  DecProp→hProp→DecProp : (P : DecProp ℓ) → hProp→DecProp (DecProp→hProp P) ≡ P
  DecProp→hProp→DecProp P i .fst = P .fst
  DecProp→hProp→DecProp P i .snd = isProp→PathP (λ i → isPropIsDecProp (P .fst)) (lem (P .fst .snd)) (P .snd) i

  hProp→DecProp→hProp : (P : hProp ℓ) → DecProp→hProp (hProp→DecProp P) ≡ P
  hProp→DecProp→hProp P = refl

  open Iso

  Iso-hProp-DecProp : Iso (hProp ℓ) (DecProp ℓ)
  Iso-hProp-DecProp = iso hProp→DecProp DecProp→hProp DecProp→hProp→DecProp hProp→DecProp→hProp

  hProp≃DecProp : hProp ℓ ≃ DecProp ℓ
  hProp≃DecProp = isoToEquiv Iso-hProp-DecProp
