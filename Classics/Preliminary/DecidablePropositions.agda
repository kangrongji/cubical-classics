{-

Facts about Decidable Propositions

Many codes here I've commited to the Cubical Agda Standard Library,
so much of this file will have need for when a new version of cubical std-lib releasing.

-}
{-# OPTIONS --safe #-}
module Classics.Preliminary.DecidablePropositions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty

open import Cubical.Relation.Nullary


private
  variable
    ℓ ℓ' : Level


-- Decidable propositions

DecProp : (ℓ : Level) → Type (ℓ-suc ℓ)
DecProp ℓ = Σ[ P ∈ hProp ℓ ] Dec (P .fst)

isPropIsDecProp : (P : hProp ℓ) → isProp (Dec (P .fst))
isPropIsDecProp P = isPropDec (P .snd)

isSetDecProp : isSet (DecProp ℓ)
isSetDecProp = isOfHLevelΣ 2 isSetHProp (λ P → isProp→isSet (isPropIsDecProp P))


-- Back and forth between boolean value and decidable propositions

Bool→Type* : Bool → Type ℓ
Bool→Type* true  = Unit*
Bool→Type* false = ⊥*

DecBool→Type* : (x : Bool) → Dec (Bool→Type* {ℓ = ℓ} x)
DecBool→Type* true  = yes tt*
DecBool→Type* false = no  λ()

isPropBool→Type* : (x : Bool) → isProp (Bool→Type* {ℓ = ℓ} x)
isPropBool→Type* true = isContr→isProp isContrUnit*

Bool→Dec→Bool* : (x : Bool) → Dec→Bool (DecBool→Type* {ℓ = ℓ} x) ≡ x
Bool→Dec→Bool* true  = refl
Bool→Dec→Bool* false = refl

P→[Dec→Bool→Type*-P] : (P : Type ℓ)(dec : Dec P) → P → Bool→Type* {ℓ = ℓ'} (Dec→Bool dec)
P→[Dec→Bool→Type*-P] _ (yes p) _ = tt*
P→[Dec→Bool→Type*-P] _ (no ¬p) x = Empty.rec (¬p x)

[Dec→Bool→Type*-P]→P : (P : Type ℓ)(dec : Dec P) → Bool→Type* {ℓ = ℓ'} (Dec→Bool dec) → P
[Dec→Bool→Type*-P]→P _ (yes p) _ = p

[DecProp→Bool→Type*-P]≃P : (P : Type ℓ)(h : isProp P)(dec : Dec P) → Bool→Type* {ℓ = ℓ'} (Dec→Bool dec) ≃ P
[DecProp→Bool→Type*-P]≃P P h dec =
  propBiimpl→Equiv (isPropBool→Type* _) h ([Dec→Bool→Type*-P]→P _ dec) (P→[Dec→Bool→Type*-P] _ dec)

[DecProp→Bool→Type*-P]≡P : (P : Type ℓ)(h : isProp P)(dec : Dec P) → Bool→Type* {ℓ = ℓ} (Dec→Bool dec) ≡ P
[DecProp→Bool→Type*-P]≡P P h dec = ua ([DecProp→Bool→Type*-P]≃P P h dec)


-- The type of boolean value is equivalent to the type of decidable propositions

Bool→DecProp : Bool → DecProp ℓ
Bool→DecProp b = (Bool→Type* b , isPropBool→Type* b) , DecBool→Type* b

DecProp→Bool : DecProp ℓ → Bool
DecProp→Bool P = Dec→Bool (P .snd)

Bool→DecProp→Bool : (x : Bool) → DecProp→Bool (Bool→DecProp {ℓ = ℓ} x) ≡ x
Bool→DecProp→Bool = Bool→Dec→Bool*

DecProp→Bool→DecProp : (P : DecProp ℓ) → Bool→DecProp (DecProp→Bool P) ≡ P
DecProp→Bool→DecProp ((P , isPropP) , decP) i .fst .fst = [DecProp→Bool→Type*-P]≡P _ isPropP decP i
DecProp→Bool→DecProp P i .fst .snd =
  isProp→PathP (λ i → isPropIsProp {A = DecProp→Bool→DecProp P i .fst .fst})
    (Bool→DecProp (DecProp→Bool P) .fst .snd) (P .fst .snd) i
DecProp→Bool→DecProp P i .snd =
  isProp→PathP (λ i → isPropIsDecProp (DecProp→Bool→DecProp P i .fst))
    (Bool→DecProp (DecProp→Bool P) .snd) (P .snd) i

open Iso

Iso-Bool-DecProp : Iso Bool (DecProp ℓ)
Iso-Bool-DecProp = iso Bool→DecProp DecProp→Bool DecProp→Bool→DecProp Bool→DecProp→Bool

Bool≃DecProp : Bool ≃ DecProp ℓ
Bool≃DecProp = isoToEquiv Iso-Bool-DecProp
