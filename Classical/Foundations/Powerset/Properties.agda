{-

Properties of Subsets

-}
{-# OPTIONS --safe #-}
module Classical.Foundations.Powerset.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Axioms
open import Classical.Foundations.Powerset.Base
open import Classical.Foundations.Powerset.Membership
open import Classical.Foundations.Powerset.Boolean

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ
    Y : Type ℓ'


module _ ⦃ 🤖 : Oracle ⦄ where


  {-

    Singleton Subset

  -}

  -- Subset with one-element

  [_] : X → ℙ X
  [_] x = specify λ y → ∥ x ≡ y ∥ , squash

  x∈[x] : {x : X} → x ∈ [ x ]
  x∈[x] {x = x} = Inhab→∈ (λ y → ∥ x ≡ y ∥ , squash) ∣ refl ∣

  y∈[x]→∥x≡y∥ : {x y : X} → y ∈ [ x ] → ∥ x ≡ y ∥
  y∈[x]→∥x≡y∥ {x = x} = ∈→Inhab (λ y → ∥ x ≡ y ∥ , squash)

  A⊆[x]→A≡∅/[x] : {A : ℙ X}{x : X} → A ⊆ [ x ] → (A ≡ ∅) ⊎ (A ≡ [ x ])
  A⊆[x]→A≡∅/[x] {X = X} {A = A} {x = x} A⊆[x] = case-split (dichotomy∈ x A)
    where
    case-split : Dichotomy∈ x A → _
    case-split (yeah x∈A) = inr (bi⊆→≡ A⊆[x] [x]⊆A)
      where
      [x]⊆A : [ x ] ⊆ A
      [x]⊆A y∈[x] = Prop.rec (isProp∈ A)
        (λ x≡y → subst (_∈ A) x≡y x∈A)
        (y∈[x]→∥x≡y∥ y∈[x])
    case-split (nope x∉A) = inl (A≡∅ (λ y → ¬∈→∉ {A = A} (∀¬x∈A y)))
      where
      ∀¬x∈A : (y : X) → ¬ y ∈ A
      ∀¬x∈A y y∈A = Prop.rec isProp⊥
        (λ x≡y → ∉→¬∈ {A = A} x∉A (subst (_∈ A) (sym x≡y) y∈A))
        (y∈[x]→∥x≡y∥ (A⊆[x] y∈A))

  A∈S→[A]⊆S : {A : ℙ X}{S : ℙ (ℙ X)} → A ∈ S → [ A ] ⊆ S
  A∈S→[A]⊆S {S = S} A∈S B∈[A] =
    Prop.rec (isProp∈ S) (λ A≡B → subst (_∈ S) A≡B A∈S) (y∈[x]→∥x≡y∥ B∈[A])

  [A]⊆S→A∈S : {A : ℙ X}{S : ℙ (ℙ X)} → [ A ] ⊆ S → A ∈ S
  [A]⊆S→A∈S [A]⊆S = [A]⊆S x∈[x]


  {-

    Image and Preimage under Functions

  -}

  image : (Y → X) → ℙ Y → ℙ X
  image {Y = Y} f A = specify λ x → ∥ Σ[ y ∈ Y ] (y ∈ A) × (f y ≡ x) ∥ , squash

  preimage : (Y → X) → ℙ X → ℙ Y
  preimage f A y = A (f y)



  {-

    The Subset of ℙ X "Represented" by x ∈ X

  -}

  rep : (x : X) → ℙ (ℙ X)
  rep x A = A x

  x∈A≡A∈repx : {x : X}{A : ℙ X} → x ∈ A ≡ A ∈ rep x
  x∈A≡A∈repx = refl

  ∩-∈rep : {x : X}(A B : ℙ X) → A ∈ rep x → B ∈ rep x → (A ∩ B) ∈ rep x
  ∩-∈rep = ∈→∈∩
