{-

Powerset under decide

-}
{-# OPTIONS --safe #-}
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
open import Cubical.Data.Sum
open import Cubical.Data.Empty as Empty

open import Cubical.HITs.PropositionalTruncation as Prop hiding (map)

open import Cubical.Relation.Nullary

open import Classics.Axioms.ExcludedMiddle

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ
    Y : Type ℓ'

-- Useful renaming

Prop = Bool
isSetProp = isSetBool

type : Prop → Type _
type = Bool→Type

bool = Dec→Bool

module Powerset (decide : LEM) where

  -- The powerset construction,
  -- well-behaved only when LEM is allowed.
  ℙ : Type ℓ → Type ℓ
  ℙ X = X → Prop

  isSetℙ : isSet (ℙ X)
  isSetℙ = isSetΠ λ _ → isSetProp

  _∈_ : X → ℙ X → Type _
  x ∈ A = A x ≡ true

  _∉_ : X → ℙ X → Type _
  x ∉ A = A x ≡ false

  infix 5 _∈_
  infix 5 _∉_

  isProp∈ : {x : X}{A : ℙ X} → isProp (x ∈ A)
  isProp∈ = isSetProp _ _

  isProp∉ : {x : X}{A : ℙ X} → isProp (x ∉ A)
  isProp∉ = isSetProp _ _

  dichotomy∈ : (x : X)(A : ℙ X) → (x ∈ A) ⊎ (x ∉ A)
  dichotomy∈ x A = dichotomyBool (A x)

  -- The specification operator `sub`,
  -- transforming a predicate into the subset of elements that satisfying it,
  -- which in certain sense realizes the axiom of separation.
  sub : (X → hProp ℓ) → ℙ X
  sub P x = bool (decide (P x .snd))

  module _
    (P : X → hProp ℓ){x : X} where

    ∈→Inhab : x ∈ sub P → P x .fst
    ∈→Inhab q with decide (P x .snd)
    ... | yes p = p
    ... | no ¬p = Empty.rec (false≢true q)

    Inhab→∈ : P x .fst → x ∈ sub P
    Inhab→∈ p with decide (P x .snd)
    ... | yes _ = refl
    ... | no ¬p = Empty.rec (¬p p)

    ∉→Empty : x ∉ sub P → ¬ P x .fst
    ∉→Empty q with decide (P x .snd)
    ... | yes p = Empty.rec (true≢false q)
    ... | no ¬p = ¬p

    Empty→∉ : ¬ P x .fst → x ∉ sub P
    Empty→∉ ¬p with decide (P x .snd)
    ... | yes p = Empty.rec (¬p p)
    ... | no ¬p = refl

  _∈?_ : X → ℙ X → Prop
  x ∈? A = A x

  infix 6 _∈?_

  _⊆_ : ℙ X → ℙ X → Type _
  A ⊆ B = ∀ {x} → x ∈ A → x ∈ B

  infix 6 _⊆_

  isProp⊆ : {A B : ℙ X} → isProp (A ⊆ B)
  isProp⊆ {B = B} = isPropImplicitΠ (λ x → isPropΠ (λ _ → isProp∈ {x = x} {A = B}))

  ⊆-trans :{A B C : ℙ X} → A ⊆ B → B ⊆ C → A ⊆ C
  ⊆-trans A⊆B B⊆C x∈A = B⊆C (A⊆B x∈A)

  ∈⊆-trans : {x : X}{A B : ℙ X} → x ∈ A → A ⊆ B → x ∈ B
  ∈⊆-trans x∈A A⊆B = A⊆B x∈A

  ≡→⊆ : {A B : ℙ X} → A ≡ B → A ⊆ B
  ≡→⊆ p {x = x} x∈A = subst (x ∈_) p x∈A

  bi⊆→≡ : {A B : ℙ X} → A ⊆ B → B ⊆ A → A ≡ B
  bi⊆→≡ {A = A} {B = B} A⊆B B⊆A i x with dichotomy∈ x A
  ... | inl p = (p ∙ sym (A⊆B p)) i
  ... | inr p with dichotomy∈ x B
  ...   | inl q = Empty.rec {A = A ≡ B} (true≢false (sym (B⊆A q) ∙ p)) i x
  ...   | inr q = (p ∙ sym q) i

  module _
    (P : X → hProp ℓ)(Q : X → hProp ℓ') where

    ⊆→Imply : sub P ⊆ sub Q → {x : X} → P x .fst → Q x .fst
    ⊆→Imply P⊆Q p = ∈→Inhab Q (P⊆Q (Inhab→∈ P p))

    Imply→⊆ : ((x : X) → P x .fst → Q x .fst) → sub P ⊆ sub Q
    Imply→⊆ P→Q x∈P = Inhab→∈ Q (P→Q _ (∈→Inhab P x∈P))

  -- Operations on powerset

  ∅ : ℙ X
  ∅ x = false

  total : ℙ X
  total x = true

  ∁_ : ℙ X → ℙ X
  (∁ P) x = not (P x)
{-
  sub¬ : (P : X → hProp ℓ) → sub (λ x → (¬ P x .fst) , isProp¬ _) ≡ ∁ (sub P)
  sub¬ P i x with decide (P x .snd)
  ... | yes p = {!!}
  ... | no ¬p = (Inhab→∈ _ ¬p ∙ sym (cong not (Empty→∉ _ ¬p))) i
-}
  _∪_ : ℙ X → ℙ X → ℙ X
  (A ∪ B) x = A x or B x

  infixr 5 _∪_

  ∪-lUnit : (A : ℙ X) → ∅ ∪ A ≡ A
  ∪-lUnit A i x = or-identityˡ (A x) i

  ∪-rUnit : (A : ℙ X) → A ∪ ∅ ≡ A
  ∪-rUnit A i x = or-identityʳ (A x) i

  ∪-Assoc : (A B C : ℙ X) → A ∪ (B ∪ C) ≡ (A ∪ B) ∪ C
  ∪-Assoc A B C i x = or-assoc (A x) (B x) (C x) i

  _∩_ : ℙ X → ℙ X → ℙ X
  (A ∩ B) x = A x and B x

  infixr 6 _∩_

  image : (Y → X) → ℙ Y → ℙ X
  image {Y = Y} f A = sub λ x → ∥ Σ[ y ∈ Y ] (y ∈ A) × (f y ≡ x) ∥ , squash

  preimage : (Y → X) → ℙ X → ℙ Y
  preimage f A y = A (f y)

  union : ℙ (ℙ X) → ℙ X
  union {X = X} S = sub λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ , squash

  ∈union→∃ : {S : ℙ (ℙ X)}{x : X} → x ∈ union S → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥
  ∈union→∃ {X = X} {S = S} = ∈→Inhab (λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ , squash)

  ∈union : {S : ℙ (ℙ X)}{x : X} → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ → x ∈ union S
  ∈union {X = X} {S = S} = Inhab→∈ λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ , squash

  union⊆ : {S : ℙ (ℙ X)}{A : ℙ X} → ((U : ℙ X) → U ∈ S → U ⊆ A) → union S ⊆ A
  union⊆ {X = X} {S = S} {A = A} U∈S→U⊆A {x = x} x∈∪S = helper (∈union→∃ x∈∪S)
    where
    helper : ∥ Σ[ N ∈ ℙ X ] (x ∈ N) × (N ∈ S) ∥ → x ∈ A
    helper = Prop.rec (isProp∈ {A = A}) (λ (_ , x∈N , N∈S) → ∈⊆-trans {B = A} x∈N (U∈S→U⊆A _ N∈S))

  -- Subset with one-element

  [_] : X → ℙ X
  [_] x = sub λ y → ∥ x ≡ y ∥ , squash

  -- Finite subset

  data isFinSubset {ℓ : Level}{X : Type ℓ} : ℙ X → Type ℓ where
    isfin∅   : isFinSubset ∅
    isfinsuc : (x : X){A : ℙ X} → isFinSubset A → isFinSubset (A ∪ [ x ])

  isFinSubset∪ : {A B : ℙ X} → isFinSubset A → isFinSubset B → isFinSubset (A ∪ B)
  isFinSubset∪ p isfin∅ = subst isFinSubset (sym (∪-rUnit _)) p
  isFinSubset∪ p (isfinsuc y finB) =
    subst isFinSubset (sym (∪-Assoc _ _ _)) (isfinsuc y (isFinSubset∪ p finB))
