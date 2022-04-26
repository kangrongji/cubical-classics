{-

Diaconescu's theorem

Axiom of Choice implies Excluded Middle

-}
{-# OPTIONS --safe #-}
module Classical.Axioms.Diaconescu where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Relation.Nullary

open import Classical.Axioms.Choice
open import Classical.Axioms.ExcludedMiddle

private
  variable
    ℓ : Level


-- Preliminaries that don't need Axiom of Choice

module _ {P : Type ℓ}(h : isProp P) where

  -- Encode-decode argument for suspension of propositions

  Code : Susp P → Type ℓ
  Code north = Unit*
  Code south = P
  Code (merid p i) = hPropExt isPropUnit* h (λ tt* → p) (λ _ → tt*) i

  isPropCode : (x : Susp P) → isProp (Code x)
  isPropCode north = isPropUnit*
  isPropCode south = h
  isPropCode (merid p i) = isProp→PathP (λ i → isPropIsProp {A = Code (merid p i)}) isPropUnit* h i

  encode : (x : Susp P) → north ≡ x → Code x
  encode _ p = subst Code p tt*

  decode : (x : Susp P) → Code x → north ≡ x
  decode north _ = refl
  decode south p = merid p
  decode (merid p i) =
    hcomp (λ j → λ
      { (i = i0) → λ _ → refl
      ; (i = i1) → λ q → merid (h p q j) })
    (λ _ j → merid p (i ∧ j))

  decode-encode : (x : Susp P)(p : north ≡ x) → decode x (encode x p) ≡ p
  decode-encode _ p = J (λ _ q → decode _ (encode _ q) ≡ q) (λ _ → refl) p

  encode-decode : (x : Susp P)(p : Code x) → encode x (decode x p) ≡ p
  encode-decode x p = isPropCode x _ p

  Code≃ : (x : Susp P) → Code x ≃ (north ≡ x)
  Code≃ x = isoToEquiv (iso (decode x) (encode x) (decode-encode x) (encode-decode x))

  isPropΩΣP : (x : Susp P) → isProp (x ≡ x)
  isPropΩΣP north = isOfHLevelRespectEquiv 1 (Code≃ north) (isPropCode north)
  isPropΩΣP south =
    isOfHLevelRespectEquiv 1 (compEquiv (Code≃ north) (congEquiv (isoToEquiv invSuspIso))) (isPropCode north)
  isPropΩΣP (merid p i) =
    isProp→PathP (λ i → isPropIsProp {A = merid p i ≡ merid p i}) (isPropΩΣP north) (isPropΩΣP south) i

  isSetΣP : isSet (Susp P)
  isSetΣP = isOfHLevelΩ→isOfHLevel 0 isPropΩΣP

  -- Main construction

  cover : Bool → Susp P
  cover true  = north
  cover false = south

  isSetFiberCover : (x : Susp P) → isSet (fiber cover x)
  isSetFiberCover _ = isSetΣ isSetBool (λ _ → isProp→isSet (isSetΣP _ _))

  ∥cover∥Sec : (x : Susp P) → ∥ fiber cover x ∥
  ∥cover∥Sec north = ∣ true  , refl ∣
  ∥cover∥Sec south = ∣ false , refl ∣
  ∥cover∥Sec (merid p i) =
    isProp→PathP (λ i → squash {A = fiber cover (merid p i)}) (∥cover∥Sec north) (∥cover∥Sec south) i

  coverSec→DecP : ((x : Susp P) → fiber cover x) → Dec P
  coverSec→DecP sec with dichotomyBool (sec north .fst) | dichotomyBool (sec south .fst)
  ... | _ | inl q = yes (invEq (Code≃ south) path)
    where path : north ≡ south
          path = cong cover (sym q) ∙ sec south .snd
  ... | inr p | _ = yes (invEq (Code≃ south) path)
    where path : north ≡ south
          path = sym (sec north .snd) ∙ cong cover p
  ... | inl p | inr q = no (λ r → true≢false (func (Code≃ south .fst r)))
    where func : north ≡ south → true ≡ false
          func r = (sym p) ∙ (λ i → sec (r i) .fst) ∙ q

  ∥coverSec∥→DecP : ∥ ((x : Susp P) → fiber cover x) ∥ → Dec P
  ∥coverSec∥→DecP = Prop.rec (isPropDec h) coverSec→DecP


-- Diaconescu's theorem

AC→LEM : AC → LEM
AC→LEM choose h = ∥coverSec∥→DecP h (choose (isSetΣP h) (isSetFiberCover h) (∥cover∥Sec h))
