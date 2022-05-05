{-

Some useful logical identity

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.Logic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Axioms.ExcludedMiddle

private
  variable
    ℓ ℓ' ℓ'' : Level
    X : Type ℓ
    Y : Type ℓ'


¬map : (X → Y) → ¬ Y → ¬ X
¬map f ¬y x = ¬y (f x)

→¬¬ : X → ¬ ¬ X
→¬¬ x ¬x = ¬x x

∥Π∥→Π∥∥ : {Y : X → Type ℓ'}
  → ∥ ((x : X) → Y x) ∥ → (x : X) → ∥ Y x ∥
∥Π∥→Π∥∥ = Prop.rec (isPropΠ (λ _ → squash)) (λ sec → λ x → ∣ sec x ∣)

∥Π∥→Π∥∥2 : {Y : X → Type ℓ'}{Z : (x : X) → Y x → Type ℓ''}
  → ∥ ((x : X) → (y : Y x) → Z x y) ∥ → (x : X) → (y : Y x) → ∥ Z x y ∥
∥Π∥→Π∥∥2 = Prop.rec (isPropΠ2 (λ _ _ → squash)) (λ sec → λ x y → ∣ sec x y ∣)


module ClassicalLogic (decide : LEM) where

  open DoubleNegationElim decide

  module _
    {P : X → Type ℓ' }(isPropP : (x : X) → isProp (P x))
    {Q : X → Type ℓ''}(isPropQ : (x : X) → isProp (Q x))
    where

    ¬Σ×→∀⊎¬ : ¬ (Σ[ x ∈ X ] P x × Q x) → (x : X) → (¬ P x) ⊎ (¬ Q x)
    ¬Σ×→∀⊎¬ ¬∃× x with decide (isPropP x) | decide (isPropQ x)
    ... | no ¬p | _ = inl ¬p
    ... | _ | no ¬q = inr ¬q
    ... | yes p | yes q = Empty.rec (¬∃× (x , p , q))

    ¬Σ¬×→∀⊎¬ : ¬ (Σ[ x ∈ X ] (¬ P x) × Q x) → (x : X) → (P x) ⊎ (¬ Q x)
    ¬Σ¬×→∀⊎¬ ¬∃¬× x with decide (isPropΠ {A = P x} (λ _ → isProp⊥)) | decide (isPropQ x)
    ... | no ¬¬p | _ = inl (¬¬elim (isPropP x) ¬¬p)
    ... | _ | no ¬q = inr ¬q
    ... | yes ¬p | yes q = Empty.rec (¬∃¬× (x , ¬p , q))

    ¬∃×→∀+¬ : ¬ ∥ Σ[ x ∈ X ] P x × Q x ∥ → (x : X) → ∥ (¬ P x) ⊎ (¬ Q x) ∥
    ¬∃×→∀+¬ f x = ∣ ¬Σ×→∀⊎¬ (f ∘ ∣_∣) x ∣

    ¬∃¬×→∀+¬ : ¬ ∥ Σ[ x ∈ X ] (¬ P x) × Q x ∥ → (x : X) → ∥ (P x) ⊎ (¬ Q x) ∥
    ¬∃¬×→∀+¬ f x = ∣ ¬Σ¬×→∀⊎¬ (f ∘ ∣_∣) x ∣
