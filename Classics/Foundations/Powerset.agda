{-

Powerset under decide

-}
{-# OPTIONS --allow-unsolved-metas #-}
module Classics.Foundations.Powerset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism hiding (section)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Data.Sigma
open import Cubical.Data.Bool

open import Cubical.HITs.PropositionalTruncation as Prop hiding (map)

open import Cubical.Relation.Nullary

open import Classics.Axioms.ExcludedMiddle

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ
    Y : Type ℓ'

Prop = Bool
isSetProp = isSetBool

module Powerset (decide : LEM) where

  ℙ : Type ℓ → Type ℓ
  ℙ X = X → Prop

  isSetℙ : isSet (ℙ X)
  isSetℙ = isSetΠ λ _ → isSetProp

  infix 6 _∈_

  _∈_ : X → ℙ X → Type _
  x ∈ A = Bool→Type (A x)

  isProp∈ : {x : X}{A : ℙ X} → isProp (x ∈ A)
  isProp∈ = {!!}

  sub : (X → hProp ℓ) → ℙ X
  sub P x = Dec→Bool (decide (P x .snd))

  module _
    (P : X → hProp ℓ){x : X} where

    ∈→Inhab : x ∈ sub P → P x .fst
    ∈→Inhab = {!!}

    Inhab→∈ : P x .fst → x ∈ sub P
    Inhab→∈ = {!!}

  infix 6 _∈?_

  _∈?_ : X → ℙ X → Prop
  x ∈? A = A x

  _⊆_ : ℙ X → ℙ X → Type _
  A ⊆ B = ∀ {x} → x ∈ A → x ∈ B

  infix 6 _⊆_

  isProp⊆ : {A B : ℙ X} → isProp (A ⊆ B)
  isProp⊆ {B = B} = isPropImplicitΠ (λ x → isPropΠ (λ _ → isProp∈ {x = x} {A = B}))

  module _
    (P : X → hProp ℓ)(Q : X → hProp ℓ') where

    ⊆→Imply : sub P ⊆ sub Q → (x : X) → P x .fst → Q x .fst
    ⊆→Imply P⊆Q _ p = ∈→Inhab Q (P⊆Q (Inhab→∈ P p))

    Imply→⊆ : ((x : X) → P x .fst → Q x .fst) → sub P ⊆ sub Q
    Imply→⊆ P→Q x∈P = Inhab→∈ Q (P→Q _ (∈→Inhab P x∈P))

    subEquiv : sub P ≡ sub Q → (x : X) → P x .fst ≃ Q x .fst
    subEquiv = {!!}

  bi⊆→≡ : {A B : ℙ X} → A ⊆ B → B ⊆ A → A ≡ B
  bi⊆→≡ p q = {!!}

  [_] : X → ℙ X
  [_] x = sub λ y → ∥ x ≡ y ∥ , squash

  -- Algebraic operations on powerset
  -- They form a Boolean algebra.

  ∅ : ℙ X
  ∅ x = false

  total : ℙ X
  total x = true

  compdecideent : ℙ X → ℙ X
  compdecideent P x = not (P x)

  _-_ : ℙ X → ℙ X → ℙ X
  _-_ = {!!}

  --sub¬ : (P : X → hProp ℓ) → sub (λ x → ¬ P x .fst , _) ≡ compdecideent (sub P)
  --sub¬ = {!!}

  _∪_ : ℙ X → ℙ X → ℙ X
  (A ∪ B) x = A x or B x

  _∩_ : ℙ X → ℙ X → ℙ X
  (A ∩ B) x = A x and B x

  image : (Y → X) → ℙ X
  image f = sub λ x → ∥ fiber f x ∥ , squash

  preimage : (Y → X) → ℙ X → ℙ Y
  preimage f A y = A (f y)

  union : ℙ (ℙ X) → ℙ X
  union {X = X} S = sub λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ , squash

  ∈union : {S : ℙ (ℙ X)}{x : X} → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ → x ∈ union S
  ∈union {X = X} {S = S} = Inhab→∈ λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ , squash

  union⊆ : {S : ℙ (ℙ X)}{A : ℙ X} → ((U : ℙ X) → U ∈ S → U ⊆ A) → union S ⊆ A
  union⊆ = {!!}

  data isFinSubset {ℓ : Level}{X : Type ℓ} : ℙ X → Type ℓ where
    isfin∅   : isFinSubset ∅
    isfinsuc : (x : X)(A : ℙ X) → isFinSubset A → isFinSubset (A ∪ [ x ])

  isFinSubset∪ : {A B : ℙ X} → isFinSubset A → isFinSubset B → isFinSubset (A ∪ B)
  isFinSubset∪ = {!!}
