{-

Impredicativity

-}
{-# OPTIONS --safe #-}
module Classics.Foundations.Impredicativity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool
open import Cubical.Relation.Nullary

open import Classics.Preliminary.DecidablePropositions
open import Classics.Axioms.ExcludedMiddle

private
  variable
    ℓ : Level
    X : Type ℓ


-- A formulation of subobject classifier

isSubobjectClassifier : Type ℓ → Typeω
isSubobjectClassifier Ω = {ℓ : Level}{X : Type ℓ} → (X → Ω) ≃ (X → hProp ℓ)


-- Renaming to emphasize Prop is a subobject classifier in classical world

Prop : Type ℓ-zero
Prop = Bool

isSetProp : isSet Prop
isSetProp = isSetBool

type : Prop → Type ℓ
type = Bool→Type*

prop : Prop → hProp ℓ
prop P = Bool→DecProp P .fst

bool : Dec X → Prop
bool = Dec→Bool


module Impredicativity (decide : LEM) where

  -- Under LEM, all propositions are decidable,
  -- and more precisely,
  -- the type of propositions is equivalent to the type of decidable propositions
  -- (of a given universe level ℓ).

  hProp→DecProp : hProp ℓ → DecProp ℓ
  hProp→DecProp P = P , decide (P .snd)

  DecProp→hProp : DecProp ℓ → hProp ℓ
  DecProp→hProp = fst

  DecProp→hProp→DecProp : (P : DecProp ℓ) → hProp→DecProp (DecProp→hProp P) ≡ P
  DecProp→hProp→DecProp P i .fst = P .fst
  DecProp→hProp→DecProp P i .snd =
    isProp→PathP (λ i → isPropIsDecProp (P .fst)) (decide (P .fst .snd)) (P .snd) i

  hProp→DecProp→hProp : (P : hProp ℓ) → DecProp→hProp (hProp→DecProp P) ≡ P
  hProp→DecProp→hProp P = refl

  open Iso

  Iso-hProp-DecProp : Iso (hProp ℓ) (DecProp ℓ)
  Iso-hProp-DecProp = iso hProp→DecProp DecProp→hProp DecProp→hProp→DecProp hProp→DecProp→hProp

  hProp≃DecProp : hProp ℓ ≃ DecProp ℓ
  hProp≃DecProp = isoToEquiv Iso-hProp-DecProp


  -- The type Prop is a subobject classifier

  Iso-Prop-hProp : Iso Prop (hProp ℓ)
  Iso-Prop-hProp = compIso Iso-Bool-DecProp (invIso Iso-hProp-DecProp)

  Prop≃hProp : Prop ≃ hProp ℓ
  Prop≃hProp = isoToEquiv Iso-Prop-hProp

  isSubobjectClassifierProp : isSubobjectClassifier Prop
  isSubobjectClassifierProp = equiv→ (idEquiv _) Prop≃hProp
