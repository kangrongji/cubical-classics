{-

Law of Excluded Middle

-}
{-# OPTIONS --safe #-}
module Classical.Axioms.ExcludedMiddle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions
  hiding (isPropIsDecProp)

open import Classical.Preliminary.DecidablePropositions
open import Classical.Axioms.Resizing

private
  variable
    ℓ : Level


-- Binary operation for being inequal

_≢_ : {X : Type ℓ}(x y : X) → Type ℓ
x ≢ y = ¬ x ≡ y

isProp≢ : {X : Type ℓ}{x y : X} → isProp (x ≢ y)
isProp≢ = isProp¬ _


-- Law of Excluded Middle and Double Negation Elimination
-- (abbreviated as LEM and DNE respectively)

-- The "per universe" version

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
LEMOfLevel→DNEOfLevel decide isPropP ¬¬p with decide isPropP
... | yes p = p
... | no ¬p = Empty.rec (¬¬p ¬p)

DNEOfLevel→LEMOfLevel : DNEOfLevel ℓ → LEMOfLevel ℓ
DNEOfLevel→LEMOfLevel elim¬¬ {P = P} isPropP = elim¬¬ (isPropDec isPropP) ¬¬dec
  where
  ¬¬dec : ¬ ¬ Dec P
  ¬¬dec ¬dec = ¬dec (yes (elim¬¬ isPropP λ ¬p → ¬dec (no ¬p)))


-- The universal polymorphic or "global" version

LEM : Typeω
LEM = {ℓ : Level} → LEMOfLevel ℓ

DNE : Typeω
DNE = {ℓ : Level} → DNEOfLevel ℓ

LEM→DNE : LEM → DNE
LEM→DNE p = LEMOfLevel→DNEOfLevel p

DNE→LEM : DNE → LEM
DNE→LEM p = DNEOfLevel→LEMOfLevel p


{-

  Some corollarie of LEM

-}

open Iso

module _ (decide : LEM) where

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

  Iso-hProp-DecProp : Iso (hProp ℓ) (DecProp ℓ)
  Iso-hProp-DecProp = iso hProp→DecProp DecProp→hProp DecProp→hProp→DecProp hProp→DecProp→hProp

  hProp≃DecProp : hProp ℓ ≃ DecProp ℓ
  hProp≃DecProp = isoToEquiv Iso-hProp-DecProp


  -- The type Prop is a subobject classifier

  Iso-Bool-hProp : Iso Bool (hProp ℓ)
  Iso-Bool-hProp = compIso Iso-Bool-DecProp (invIso Iso-hProp-DecProp)

  Bool≃hProp : Bool ≃ hProp ℓ
  Bool≃hProp = isoToEquiv Iso-Bool-hProp

  isSubobjectClassifierBool : isSubobjectClassifier Bool
  isSubobjectClassifierBool = getSubobjectClassifier Bool≃hProp


-- Law of Excluded Middle implies Propositional Resizing

open DropProp

LEM→Drop : LEM → Drop
LEM→Drop decide P .lower = Iso-Bool-hProp decide .fun (Iso-Bool-hProp decide .inv P)
LEM→Drop decide (P , h) .dropEquiv = invEquiv ([DecProp→Bool→Type*-P]≃P P h _)

LEM→Resizing : LEM → Resizing
LEM→Resizing decide = Drop→Resizing (LEM→Drop decide)
