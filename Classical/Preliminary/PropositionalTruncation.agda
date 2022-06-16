{-

Facts about Propositional Truncation

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.PropositionalTruncation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation public

private
  variable
    ℓ ℓ' : Level
    A B C D E : Type ℓ


map3 : (A → B → C → D) → (∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → ∥ D ∥₁)
map3 f = rec (isPropΠ2 λ _ _ → squash₁) (map2 ∘ f)

map4 : (A → B → C → D → E) → (∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁ → ∥ D ∥₁ → ∥ E ∥₁)
map4 f = rec (isPropΠ3 λ _ _ _ → squash₁) (map3 ∘ f)
