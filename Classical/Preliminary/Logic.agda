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

open import Classical.Axioms

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
  → ∥ ((x : X) → Y x) ∥₁ → (x : X) → ∥ Y x ∥₁
∥Π∥→Π∥∥ = Prop.rec (isPropΠ (λ _ → squash₁)) (λ sec → λ x → ∣ sec x ∣₁)

∥Π∥→Π∥∥2 : {Y : X → Type ℓ'}{Z : (x : X) → Y x → Type ℓ''}
  → ∥ ((x : X) → (y : Y x) → Z x y) ∥₁ → (x : X) → (y : Y x) → ∥ Z x y ∥₁
∥Π∥→Π∥∥2 = Prop.rec (isPropΠ2 (λ _ _ → squash₁)) (λ sec → λ x y → ∣ sec x y ∣₁)


¬Σ→∀¬ : {P : X → Type ℓ'} → ¬ (Σ[ x ∈ X ] P x) → (x : X) → ¬ P x
¬Σ→∀¬ f x p = f (x , p)

¬∃→∀¬ : {P : X → Type ℓ'} → ¬ ∥ Σ[ x ∈ X ] P x ∥₁ → (x : X) → ¬ P x
¬∃→∀¬ f = ¬Σ→∀¬ ((¬map ∣_∣₁) f)

¬Σ→∀¬2 : {Y : X → Type ℓ'}{Z : (x : X) → Y x → Type ℓ''}
  → ¬ (Σ[ x ∈ X ] Σ[ y ∈ Y x ] Z x y)
  → (x : X) → (y : Y x) → ¬ Z x y
¬Σ→∀¬2 f x = ¬Σ→∀¬ (¬Σ→∀¬ f x)

¬∃→∀¬2 : {Y : X → Type ℓ'}{Z : (x : X) → Y x → Type ℓ''}
  → ¬ ∥ Σ[ x ∈ X ] Σ[ y ∈ Y x ] Z x y ∥₁
  → (x : X) → (y : Y x) → ¬ Z x y
¬∃→∀¬2 f = ¬Σ→∀¬2 ((¬map ∣_∣₁) f)


takeOut∥Σ∥ : {P : X → Type ℓ'} → ∥ Σ[ x ∈ X ] ∥ P x ∥₁ ∥₁ → ∥ Σ[ x ∈ X ] P x ∥₁
takeOut∥Σ∥ = Prop.rec squash₁ (λ (x , ∥p∥) → Prop.map (λ p → x , p) ∥p∥)


module _ ⦃ 🤖 : Oracle ⦄ where

  open Oracle 🤖


  ¬¬elim : DNE
  ¬¬elim = LEM→DNE decide


  module _
    {P : X → Type ℓ'}
    where

    ¬∀¬→∃ : ¬ ((x : X) → ¬ P x) → ∥ Σ[ x ∈ X ] P x ∥₁
    ¬∀¬→∃ f = ¬¬elim squash₁ (¬map ¬∃→∀¬ f)


  module _
    {P : X → Type ℓ'}(isPropP : (x : X) → isProp (P x))
    where

    ¬∀→∃¬ : ¬ ((x : X) → P x) → ∥ Σ[ x ∈ X ] ¬ P x ∥₁
    ¬∀→∃¬ f = ¬∀¬→∃ (¬map helper f)
      where
      helper : ((x : X) → ¬ ¬ P x) → (x : X) → P x
      helper f x = ¬¬elim (isPropP _) (f x)


  module _
    {Y : X → Type ℓ'}
    {P : (x : X) → Y x → Type ℓ''}
    (isPropP : (x : X) → (y : Y x) → isProp (P x y))
    where

    ¬∀→∃¬2 : ¬ ((x : X) → (y : Y x) → P x y) → ∥ Σ[ x ∈ X ] Σ[ y ∈ Y x ] ¬ P x y ∥₁
    ¬∀→∃¬2 f = takeOut∥Σ∥ helper
      where
      helper : ∥ Σ[ x ∈ X ] ∥ Σ[ y ∈ Y x ] ¬ P x y ∥₁ ∥₁
      helper = Prop.map
        (λ (x , ¬p) → x , ¬∀→∃¬ (isPropP _) ¬p)
        (¬∀→∃¬ (λ _ → isPropΠ (λ _ → isPropP _ _)) f)


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


    ¬Σ×→∀→¬ : ¬ (Σ[ x ∈ X ] P x × Q x) → (x : X) → P x → (¬ Q x)
    ¬Σ×→∀→¬ ¬∃× x p with ¬Σ×→∀⊎¬ ¬∃× x
    ... | inl ¬p = Empty.rec (¬p p)
    ... | inr ¬q = ¬q


    ¬∃×→∀+¬ : ¬ ∥ Σ[ x ∈ X ] P x × Q x ∥₁ → (x : X) → ∥ (¬ P x) ⊎ (¬ Q x) ∥₁
    ¬∃×→∀+¬ f x = ∣ ¬Σ×→∀⊎¬ (f ∘ ∣_∣₁) x ∣₁

    ¬∃¬×→∀+¬ : ¬ ∥ Σ[ x ∈ X ] (¬ P x) × Q x ∥₁ → (x : X) → ∥ (P x) ⊎ (¬ Q x) ∥₁
    ¬∃¬×→∀+¬ f x = ∣ ¬Σ¬×→∀⊎¬ (f ∘ ∣_∣₁) x ∣₁


    ¬∃×→∀→¬ : ¬ ∥ Σ[ x ∈ X ] P x × Q x ∥₁ → (x : X) → P x → (¬ Q x)
    ¬∃×→∀→¬ f x p = ¬Σ×→∀→¬ (f ∘ ∣_∣₁) x p
