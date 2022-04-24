{-

Some useful logical identity

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.Logic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

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
