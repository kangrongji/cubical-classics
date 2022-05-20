{-

Finiteness of Subset

-}
{-# OPTIONS --safe #-}
module Classical.Foundations.Powerset.Finiteness where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset.Base
open import Classical.Foundations.Powerset.Membership
open import Classical.Foundations.Powerset.Boolean
open import Classical.Foundations.Powerset.Properties
open import Classical.Foundations.Powerset.BigOps

private
  variable
    ℓ : Level
    X : Type ℓ


module Finiteness (decide : LEM) where

  open Base       decide
  open Membership decide
  open Boolean    decide
  open Properties decide
  open BigOps     decide


  {-

    Predicate of Finiteness

  -}

  -- Inductive definition of being finite

  data isFinSub {ℓ : Level}{X : Type ℓ} : ℙ X → Type ℓ where
    isfin∅   : isFinSub ∅
    isfinsuc : {A : ℙ X} → isFinSub A → (x : X) → isFinSub (A ∪ [ x ])
    fin-squash : {A : ℙ X} → (p q : isFinSub A) → p ≡ q


  isFinSub[x] : {x : X} → isFinSub [ x ]
  isFinSub[x] {x = x} = subst isFinSub (∪-lUnit _) (isfinsuc isfin∅ x)

  isFinSub∪ : {A B : ℙ X} → isFinSub A → isFinSub B → isFinSub (A ∪ B)
  isFinSub∪ p isfin∅ = subst isFinSub (sym (∪-rUnit _)) p
  isFinSub∪ p (isfinsuc finB y) =
    subst isFinSub (sym (∪-Assoc _ _ _)) (isfinsuc (isFinSub∪ p finB) y)
  isFinSub∪ p (fin-squash q s i) = fin-squash (isFinSub∪ p q) (isFinSub∪ p s) i

  isFinSub⊆ : {A B : ℙ X} → A ⊆ B → isFinSub B → isFinSub A
  isFinSub⊆ A⊆B isfin∅ = subst isFinSub (sym (A⊆∅→A≡∅ A⊆B)) isfin∅
  isFinSub⊆ {A = A} A⊆B (isfinsuc {A = B} finB y) =
    subst isFinSub (sym (∩-∪-rDist _ _ _) ∙ A⊆B→A∩B≡A A⊆B) (isFinSub∪ finA∩B finA∩[y])
    where
    finA∩B : isFinSub (A ∩ B)
    finA∩B = isFinSub⊆ (right∈-∩ A B) finB
    finA∩[y] : isFinSub (A ∩ [ y ])
    finA∩[y] = case-split (A⊆[x]→A≡∅/[x] (right∈-∩ A [ y ]))
      where
      case-split : (A ∩ [ y ] ≡ ∅) ⊎ (A ∩ [ y ] ≡ [ y ]) → _
      case-split (inl A∩[y]≡∅) = subst isFinSub (sym A∩[y]≡∅) isfin∅
      case-split (inr A∩[y]≡[y]) = subst isFinSub (sym A∩[y]≡[y]) isFinSub[x]
  isFinSub⊆ A⊆B (fin-squash p q i) = fin-squash (isFinSub⊆ A⊆B p) (isFinSub⊆ A⊆B q) i

