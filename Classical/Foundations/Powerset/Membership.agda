{-

The Membership and Inclusion Relation

-}
{-# OPTIONS --safe #-}
module Classical.Foundations.Powerset.Membership where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Preliminary.Logic
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset.Base

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ


module Membership (decide : LEM) where

  open Base decide


  {-

    Membership

  -}

  -- Data type to make pattern matching more clearer, :P

  data Dichotomy∈ {X : Type ℓ}(x : X)(A : ℙ X) : Type ℓ where
    yeah : x ∈ A → Dichotomy∈ x A
    nope : x ∉ A → Dichotomy∈ x A

  dichotomy∈ : (x : X)(A : ℙ X) → Dichotomy∈ x A
  dichotomy∈ x A with dichotomyBool (A x)
  ... | inl x∈A = yeah x∈A
  ... | inr x∉A = nope x∉A


  explode∈ : {Y : Type ℓ'} → {x : X}{A : ℙ X} → x ∈ A → x ∉ A → Y
  explode∈ x∈A x∉A = Empty.rec (true≢false (sym x∈A ∙ x∉A))

  ∈∉→≢ : {x y : X}{A : ℙ X} → x ∈ A → y ∉ A → ¬ x ≡ y
  ∈∉→≢ {A = A} x∈A y∉A x≡y = explode∈ {A = A} (subst (_∈ A) x≡y x∈A) y∉A


  -- Negation of membership

  module _
    {x : X}{A : ℙ X} where

    ∈→¬∉ : x ∈ A → ¬ x ∉ A
    ∈→¬∉ x∈A x∉A = explode∈ {A = A} x∈A x∉A

    ∉→¬∈ : x ∉ A → ¬ x ∈ A
    ∉→¬∈ x∉A x∈A = explode∈ {A = A} x∈A x∉A

    ¬∈→∉ : ¬ x ∈ A → x ∉ A
    ¬∈→∉ ¬x∈A with dichotomy∈ x A
    ... | yeah x∈A = Empty.rec (¬x∈A x∈A)
    ... | nope x∉A = x∉A

    ¬∉→∈ : ¬ x ∉ A → x ∈ A
    ¬∉→∈ ¬x∉A with dichotomy∈ x A
    ... | yeah x∈A = x∈A
    ... | nope x∉A = Empty.rec (¬x∉A x∉A)

    ¬¬∈→∈ : ¬ ¬ x ∈ A → x ∈ A
    ¬¬∈→∈ p = ¬∉→∈ (¬map ∉→¬∈ p)

    ¬¬∉→∉ : ¬ ¬ x ∉ A → x ∉ A
    ¬¬∉→∉ p = ¬∈→∉ (¬map ∈→¬∉ p)


  {-

    Inclusion

  -}

  ⊆-trans :{A B C : ℙ X} → A ⊆ B → B ⊆ C → A ⊆ C
  ⊆-trans A⊆B B⊆C x∈A = B⊆C (A⊆B x∈A)

  ∈⊆-trans : {x : X}{A B : ℙ X} → x ∈ A → A ⊆ B → x ∈ B
  ∈⊆-trans x∈A A⊆B = A⊆B x∈A

  ≡→⊆ : {A B : ℙ X} → A ≡ B → A ⊆ B
  ≡→⊆ p {x = x} x∈A = subst (x ∈_) p x∈A

  ⊆-refl : {A : ℙ X} → A ⊆ A
  ⊆-refl p = p

  bi⊆→≡ : {A B : ℙ X} → A ⊆ B → B ⊆ A → A ≡ B
  bi⊆→≡ {A = A} {B = B} A⊆B B⊆A i x with dichotomy∈ x A
  ... | yeah p = (p ∙ sym (A⊆B p)) i
  ... | nope p with dichotomy∈ x B
  ...   | yeah q = Empty.rec {A = A ≡ B} (true≢false (sym (B⊆A q) ∙ p)) i x
  ...   | nope q = (p ∙ sym q) i


  ∀∈+¬∈→⊆ : {A B : ℙ X} → ((x : X) → ∥ (x ∈ B) ⊎ (¬ x ∈ A) ∥) → A ⊆ B
  ∀∈+¬∈→⊆ {B = B} ∀∈+¬∈ {x = x} x∈A = Prop.rec (isProp∈ B)
    (λ { (inl x∈B) → x∈B ; (inr ¬x∈A) → Empty.rec (¬x∈A x∈A) }) (∀∈+¬∈ x)


  -- There always merely exists element outside a non-subset against another subset

  module _ {A B : ℙ X}(¬A⊆B : ¬ A ⊆ B) where

    private
      P = ∥ Σ[ x ∈ X ] (¬ x ∈ B) × (x ∈ A) ∥
      isPropP : isProp ∥ Σ[ x ∈ X ] (¬ x ∈ B) × (x ∈ A) ∥
      isPropP = squash

    open ClassicalLogic decide

    ⊈→∃ : ∥ Σ[ x ∈ X ] (¬ x ∈ B) × (x ∈ A) ∥
    ⊈→∃ with decide isPropP
    ... | yes p = p
    ... | no ¬p = Empty.rec (¬A⊆B (∀∈+¬∈→⊆
      (¬∃¬×→∀+¬ (λ _ → isProp∈ B) (λ _ → isProp∈ A) ¬p)))


  {-

    Inhabitedness

  -}

  -- Inhabitedness, namely, not being empty

  isInhabited : {X : Type ℓ} → ℙ X → Type ℓ
  isInhabited {X = X} A = ∥ Σ[ x ∈ X ] x ∈ A ∥

  isPropIsInhabited : (A : ℙ X) → isProp (isInhabited A)
  isPropIsInhabited _ = squash

  ¬isInhabited→¬x∈A : {A : ℙ X} → ¬ isInhabited A → (x : X) → x ∈ A → ⊥
  ¬isInhabited→¬x∈A ¬∈ = ¬∃→∀¬ ¬∈


  {-

    Consequences of the Axiom Schema of Specification

  -}

  -- Membership and inhabitedness

  module _
    (P : X → hProp ℓ){x : X} where

    ∈→Inhab : x ∈ specify P → P x .fst
    ∈→Inhab q with decide (P x .snd)
    ... | yes p = p
    ... | no ¬p = Empty.rec (false≢true q)

    Inhab→∈ : P x .fst → x ∈ specify P
    Inhab→∈ p with decide (P x .snd)
    ... | yes _ = refl
    ... | no ¬p = Empty.rec (¬p p)

    ∉→Empty : x ∉ specify P → ¬ P x .fst
    ∉→Empty q with decide (P x .snd)
    ... | yes p = Empty.rec (true≢false q)
    ... | no ¬p = ¬p

    Empty→∉ : ¬ P x .fst → x ∉ specify P
    Empty→∉ ¬p with decide (P x .snd)
    ... | yes p = Empty.rec (¬p p)
    ... | no ¬p = refl


  module _
    (P : X → hProp ℓ)(Q : X → hProp ℓ') where

    ⊆→Imply : specify P ⊆ specify Q → {x : X} → P x .fst → Q x .fst
    ⊆→Imply P⊆Q p = ∈→Inhab Q (P⊆Q (Inhab→∈ P p))

    Imply→⊆ : ((x : X) → P x .fst → Q x .fst) → specify P ⊆ specify Q
    Imply→⊆ P→Q x∈P = Inhab→∈ Q (P→Q _ (∈→Inhab P x∈P))
