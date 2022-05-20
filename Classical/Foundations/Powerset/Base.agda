{-

Classical Impredicative Powerset

This file introduces a "powerset", thanks to Excluded Middle,
behaving very similar to that in classical set theory.
However, I think except for a few `Boolean facts`,
most of the following results only relies on the concept of impredicativity,
and one way to formulate that is the existence of subobject classifier
(LEM or even Propostional Resizing is enough to guarantee its existence).

Everything about powerset is separated into several files in this fold.

This one is classical and impredicative.
One can find a constructive and predicative version in the standard library of Cubical Agda,
see "https://github.com/agda/cubical/blob/master/Cubical/Foundations/Powerset.agda".

-}
{-# OPTIONS --safe #-}
module Classical.Foundations.Powerset.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Prelude

private
  variable
    ℓ : Level
    X : Type ℓ


module Base (decide : LEM) where


  -- The powerset construction, namely the type of all possible "subsets",
  -- well-behaved only when one has some kind of impredicativity.

  ℙ_ : Type ℓ → Type ℓ
  ℙ X = X → Prop

  isSetℙ : isSet (ℙ X)
  isSetℙ = isSetΠ λ _ → isSetProp


  -- The specification operator `specify`,
  -- transforming a predicate into the subset of elements that satisfying it,
  -- in certain sense realizes the axiom of specification/separation in classical set theory.

  specify : {ℓ : Level} → (X → hProp ℓ) → ℙ X
  specify P x = bool (decide (P x .snd))


  -- The Mmpty Subset

  ∅ : ℙ X
  ∅ x = false

  -- The Total Subset

  total : ℙ X
  total x = true


  -- Membership Relation

  _∈_ : X → ℙ X → Type
  x ∈ A = A x ≡ true

  infix 6 _∈_

  isProp∈ : {x : X}(A : ℙ X) → isProp (x ∈ A)
  isProp∈ _ = isSetProp _ _

  -- Non-Membership

  _∉_ : X → ℙ X → Type
  x ∉ A = A x ≡ false

  infix 6 _∉_

  isProp∉ : {x : X}(A : ℙ X) → isProp (x ∉ A)
  isProp∉ _ = isSetProp _ _

  -- Inclusion Relation of Subsets

  _⊆_ : {X : Type ℓ} → ℙ X → ℙ X → Type ℓ
  A ⊆ B = ∀ {x} → x ∈ A → x ∈ B

  infix 7 _⊆_

  isProp⊆ : {A B : ℙ X} → isProp (A ⊆ B)
  isProp⊆ {B = B} = isPropImplicitΠ (λ x → isPropΠ (λ _ → isProp∈ B))


  -- Complement of Subset

  ∁_ : ℙ X → ℙ X
  (∁ P) x = not (P x)

  infixr 10 ∁_

  -- Binary Union

  _∪_ : ℙ X → ℙ X → ℙ X
  (A ∪ B) x = A x or B x

  infixr 8 _∪_

  -- Binary Intersection

  _∩_ : ℙ X → ℙ X → ℙ X
  (A ∩ B) x = A x and B x

  infixr 9 _∩_
