{-

Facts about Suspension

Copied from unreleased new version of cubical std-lib.
Will be abandoned if new release comes public.

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.Susp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Susp


-- inversion

invSusp : ∀ {ℓ} {A : Type ℓ} → Susp A → Susp A
invSusp north = south
invSusp south = north
invSusp (merid a i) = merid a (~ i)

invSusp² : ∀ {ℓ} {A : Type ℓ} (x : Susp A) → invSusp (invSusp x) ≡ x
invSusp² north = refl
invSusp² south = refl
invSusp² (merid a i) = refl

invSuspIso : ∀ {ℓ} {A : Type ℓ} → Iso (Susp A) (Susp A)
invSuspIso = iso invSusp invSusp invSusp² invSusp²

invSusp≃ : ∀ {ℓ} {A : Type ℓ} → Susp A ≃ Susp A
invSusp≃ = isoToEquiv invSuspIso
