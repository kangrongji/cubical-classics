{-

Impredicative Powerset

This file introduces a "powerset", thanks to Excluded Middle,
behaving very similar to that in classical set theory.
I think most of the results only relies on impredicativity,
so that maybe axiom as Propositional Resizing is enough
to recover these useful properties.

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classics.Foundations.Powerset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Relation.Nullary

open import Classics.Preliminary.Bool
open import Classics.Preliminary.Logic
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

  {-

    Basics

  -}

  -- The powerset construction,
  -- well-behaved only when LEM is allowed.
  ℙ : Type ℓ → Type ℓ
  ℙ X = X → Prop

  isSetℙ : isSet (ℙ X)
  isSetℙ = isSetΠ λ _ → isSetProp

  infix 5 _∈_
  infix 5 _∉_
  infix 6 _∈?_
  infix 6 _⊆_
  infixr 5 _∪_
  infixr 6 _∩_


  {-

    The Membership and Subset Relation

  -}

  _∈_ : X → ℙ X → Type _
  x ∈ A = A x ≡ true

  _∉_ : X → ℙ X → Type _
  x ∉ A = A x ≡ false

  isProp∈ : {x : X}{A : ℙ X} → isProp (x ∈ A)
  isProp∈ = isSetProp _ _

  isProp∉ : {x : X}{A : ℙ X} → isProp (x ∉ A)
  isProp∉ = isSetProp _ _

  dichotomy∈ : (x : X)(A : ℙ X) → (x ∈ A) ⊎ (x ∉ A)
  dichotomy∈ x A = dichotomyBool (A x)

  explode∈ : {x : X}{A : ℙ X} → x ∈ A → x ∉ A → Y
  explode∈ x∈A x∉A = Empty.rec (true≢false (sym x∈A ∙ x∉A))

  -- Negation of membership
  module _
    {x : X}{A : ℙ X} where

    ∈→¬∉ : x ∈ A → ¬ x ∉ A
    ∈→¬∉ x∈A x∉A = explode∈ {A = A} x∈A x∉A

    ∉→¬∈ : x ∉ A → ¬ x ∈ A
    ∉→¬∈ x∉A x∈A = explode∈ {A = A} x∈A x∉A

    ¬∈→∉ : ¬ x ∈ A → x ∉ A
    ¬∈→∉ ¬x∈A with dichotomy∈ x A
    ... | inl x∈A = Empty.rec (¬x∈A x∈A)
    ... | inr x∉A = x∉A

    ¬∉→∈ : ¬ x ∉ A → x ∈ A
    ¬∉→∈ ¬x∉A with dichotomy∈ x A
    ... | inl x∈A = x∈A
    ... | inr x∉A = Empty.rec (¬x∉A x∉A)

    ¬¬∈→∈ : ¬ ¬ x ∈ A → x ∈ A
    ¬¬∈→∈ p = ¬∉→∈ (¬map ∉→¬∈ p)

    ¬¬∉→∉ : ¬ ¬ x ∉ A → x ∉ A
    ¬¬∉→∉ p = ¬∈→∉ (¬map ∈→¬∉ p)

  _∈?_ : X → ℙ X → Prop
  x ∈? A = A x

  _⊆_ : ℙ X → ℙ X → Type _
  A ⊆ B = ∀ {x} → x ∈ A → x ∈ B

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


  {-

    Boolean Algebraic Operations

    This part doesn't need impredicativity actually.

  -}

  -- Empty and Total Subset

  ∅ : ℙ X
  ∅ x = false

  total : ℙ X
  total x = true

  x∉∅ : {x : X} → x ∉ ∅
  x∉∅ = refl

  x∈total : {x : X} → x ∈ total
  x∈total = refl

  ∅⊆A : {A : ℙ X} → ∅ ⊆ A
  ∅⊆A x∈∅ = Empty.rec (false≢true x∈∅)

  A⊆total : {A : ℙ X} → A ⊆ total
  A⊆total _ = refl

  A⊆∅ : {A : ℙ X} → ((x : X) → x ∉ A) → A ⊆ ∅
  A⊆∅ p x∈A = Empty.rec (true≢false (sym x∈A ∙ p _))

  total⊆A : {A : ℙ X} → ((x : X) → x ∈ A) → total ⊆ A
  total⊆A p _ = p _

  A≡∅ : {A : ℙ X} → ((x : X) → x ∉ A) → A ≡ ∅
  A≡∅ {A = A} p = bi⊆→≡ (A⊆∅ p) (∅⊆A {A = A})

  A≡total : {A : ℙ X} → ((x : X) → x ∈ A) → A ≡ total
  A≡total {A = A} p = bi⊆→≡ (A⊆total {A = A}) (total⊆A p)

  -- Complementary subset

  ∁_ : ℙ X → ℙ X
  (∁ P) x = not (P x)

  ∁-Unip : (A : ℙ X) → ∁ ∁ A ≡ A
  ∁-Unip A i x = notnot (A x) i

  -- Binary union

  _∪_ : ℙ X → ℙ X → ℙ X
  (A ∪ B) x = A x or B x

  ∪-lZero : (A : ℙ X) → total ∪ A ≡ total
  ∪-lZero A i x = zeroˡ (A x) i

  ∪-rZero : (A : ℙ X) → A ∪ total ≡ total
  ∪-rZero A i x = zeroʳ (A x) i

  ∪-lUnit : (A : ℙ X) → ∅ ∪ A ≡ A
  ∪-lUnit A i x = or-identityˡ (A x) i

  ∪-rUnit : (A : ℙ X) → A ∪ ∅ ≡ A
  ∪-rUnit A i x = or-identityʳ (A x) i

  ∪-Comm : (A B : ℙ X) → A ∪ B ≡ B ∪ A
  ∪-Comm A B i x = or-comm (A x) (B x) i

  ∪-Assoc : (A B C : ℙ X) → A ∪ (B ∪ C) ≡ (A ∪ B) ∪ C
  ∪-Assoc A B C i x = or-assoc (A x) (B x) (C x) i

  ∪-Idem : (A : ℙ X) → A ∪ A ≡ A
  ∪-Idem A i x = or-idem (A x) i

  ∪-left∈ : {x : X}(A B : ℙ X) → x ∈ A → x ∈ (A ∪ B)
  ∪-left∈ {x = x} _ B x∈A = (λ i → x∈A i or B x) ∙ zeroˡ _

  ∪-right∈ : {x : X}(A B : ℙ X) → x ∈ B → x ∈ (A ∪ B)
  ∪-right∈ {x = x} A _ x∈B = (λ i → A x or x∈B i) ∙ zeroʳ _

  ∪-left⊆ : (A B : ℙ X) → A ⊆ (A ∪ B)
  ∪-left⊆ A B = ∪-left∈ A B

  ∪-right⊆ : (A B : ℙ X) → B ⊆ (A ∪ B)
  ∪-right⊆ A B = ∪-right∈ A B

  -- Binary intersection

  _∩_ : ℙ X → ℙ X → ℙ X
  (A ∩ B) x = A x and B x

  ∩-lZero : (A : ℙ X) → ∅ ∩ A ≡ ∅
  ∩-lZero A i x = and-zeroˡ (A x) i

  ∩-rZero : (A : ℙ X) → A ∩ ∅ ≡ ∅
  ∩-rZero A i x = and-zeroʳ (A x) i

  ∩-lUnit : (A : ℙ X) → total ∩ A ≡ A
  ∩-lUnit A i x = and-identityˡ (A x) i

  ∩-rUnit : (A : ℙ X) → A ∩ total ≡ A
  ∩-rUnit A i x = and-identityʳ (A x) i

  ∩-Comm : (A B : ℙ X) → A ∩ B ≡ B ∩ A
  ∩-Comm A B i x = and-comm (A x) (B x) i

  ∩-Assoc : (A B C : ℙ X) → A ∩ (B ∩ C) ≡ (A ∩ B) ∩ C
  ∩-Assoc A B C i x = and-assoc (A x) (B x) (C x) i

  ∩-Idem : (A : ℙ X) → A ∩ A ≡ A
  ∩-Idem A i x = and-idem (A x) i

  ∩-∈ : {x : X}(A B : ℙ X) → x ∈ A → x ∈ B → x ∈ (A ∩ B)
  ∩-∈ A B x∈A x∈B i = x∈A i and x∈B i

  ∩-⊆ : {C : ℙ X}(A B : ℙ X) → C ⊆ A → C ⊆ B → C ⊆ (A ∩ B)
  ∩-⊆ A B C⊆A C⊆B x∈C = ∩-∈ A B (C⊆A x∈C) (C⊆B x∈C)

  -- Absorption laws

  ∪-∩-Absorp : (A B : ℙ X) → A ∪ (A ∩ B) ≡ A
  ∪-∩-Absorp A B i x = or-and-absorp (A x) (B x) i

  ∩-∪-Absorp : (A B : ℙ X) → A ∩ (A ∪ B) ≡ A
  ∩-∪-Absorp A B i x = and-or-absorp (A x) (B x) i

  -- Distribution laws

  ∪-∩-Dist : (A B C : ℙ X) → A ∪ (B ∩ C) ≡ (A ∪ B) ∩ (A ∪ C)
  ∪-∩-Dist A B C i x = or-and-dist (A x) (B x) (C x) i

  ∩-∪-Dist : (A B C : ℙ X) → A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C)
  ∩-∪-Dist A B C i x = and-or-dist (A x) (B x) (C x) i

  -- Complementation laws

  ∪-Compt : (A : ℙ X) → A ∪ (∁ A) ≡ total
  ∪-Compt A i x = or-compt (A x) i

  ∩-Compt : (A : ℙ X) → A ∩ (∁ A) ≡ ∅
  ∩-Compt A i x = and-compt (A x) i

  -- de Morgan laws

  ∪-∩-deMorgan : (A B : ℙ X) → (∁ A) ∪ (∁ B) ≡ ∁ (A ∩ B)
  ∪-∩-deMorgan A B i x = or-and-deMorgan (A x) (B x) i

  ∩-∪-deMorgan : (A B : ℙ X) → (∁ A) ∩ (∁ B) ≡ ∁ (A ∪ B)
  ∩-∪-deMorgan A B i x = and-or-deMorgan (A x) (B x) i


  {-

    Axiom Schema of Specification

  -}

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

  module _
    (P : X → hProp ℓ)(Q : X → hProp ℓ') where

    ⊆→Imply : sub P ⊆ sub Q → {x : X} → P x .fst → Q x .fst
    ⊆→Imply P⊆Q p = ∈→Inhab Q (P⊆Q (Inhab→∈ P p))

    Imply→⊆ : ((x : X) → P x .fst → Q x .fst) → sub P ⊆ sub Q
    Imply→⊆ P→Q x∈P = Inhab→∈ Q (P→Q _ (∈→Inhab P x∈P))

  {-
  sub¬ : (P : X → hProp ℓ) → sub (λ x → (¬ P x .fst) , isProp¬ _) ≡ ∁ (sub P)
  sub¬ P i x with decide (P x .snd)
  ... | yes p = {!!}
  ... | no ¬p = (Inhab→∈ _ ¬p ∙ sym (cong not (Empty→∉ _ ¬p))) i
  -}


  {-

    Singleton Subset

  -}

  -- Subset with one-element

  [_] : X → ℙ X
  [_] x = sub λ y → ∥ x ≡ y ∥ , squash

  A∈S→[A]⊆S : {A : ℙ X}{S : ℙ (ℙ X)} → A ∈ S → [ A ] ⊆ S
  A∈S→[A]⊆S = {!!}

  [A]⊆S→A∈S : {A : ℙ X}{S : ℙ (ℙ X)} → [ A ] ⊆ S → A ∈ S
  [A]⊆S→A∈S = {!!}

  {-

    Image and Preimage under Functions

  -}

  image : (Y → X) → ℙ Y → ℙ X
  image {Y = Y} f A = sub λ x → ∥ Σ[ y ∈ Y ] (y ∈ A) × (f y ≡ x) ∥ , squash

  preimage : (Y → X) → ℙ X → ℙ Y
  preimage f A y = A (f y)


  {-

    Infinitary Operations

  -}

  union : ℙ (ℙ X) → ℙ X
  union {X = X} S = sub λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ , squash

  module _
    {S : ℙ (ℙ X)}{x : X} where

    ∈union→∃ : x ∈ union S → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥
    ∈union→∃ = ∈→Inhab (λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ , squash)

    ∈union : ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ → x ∈ union S
    ∈union = Inhab→∈ λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥ , squash

    --∉union→∀ : x ∉ union S → (A : ℙ X) → A ∈ S → x ∉ A
    --∉union→∀ = {!!}

    ∉union : ((A : ℙ X) → A ∈ S → x ∉ A) → x ∉ union S
    ∉union p = ¬∈→∉ {A = union S} (¬map ∈union→∃ helper)
      where
      helper : ¬ ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥
      helper = Prop.rec isProp⊥ (λ (A , x∈A , A∈S) → explode∈ {A = A} x∈A (p _ A∈S))

  union∅ : union {X = X} ∅ ≡ ∅
  union∅ = A≡∅ (λ U → ∉union (helper U))
    where
    helper : (x : X) → (A : ℙ X) → A ∈ ∅ → x ∉ A
    helper _ A A∈∅ = explode∈ {x = A} A∈∅ (x∉∅ {x = A})

  union⊆ : {S : ℙ (ℙ X)}{A : ℙ X} → ((U : ℙ X) → U ∈ S → U ⊆ A) → union S ⊆ A
  union⊆ {X = X} {S = S} {A = A} U∈S→U⊆A {x = x} x∈∪S = helper (∈union→∃ x∈∪S)
    where
    helper : ∥ Σ[ N ∈ ℙ X ] (x ∈ N) × (N ∈ S) ∥ → x ∈ A
    helper = Prop.rec (isProp∈ {A = A}) (λ (_ , x∈N , N∈S) → ∈⊆-trans {B = A} x∈N (U∈S→U⊆A _ N∈S))

  union∪ : {S T : ℙ (ℙ X)} → union (S ∪ T) ≡ union S ∪ union T
  union∪ = {!!}

  union∪-left⊆ : {S T : ℙ (ℙ X)} → union S ⊆ union (S ∪ T)
  union∪-left⊆ = {!!}

  union[A] : {A : ℙ X} → union [ A ] ≡ A
  union[A] = {!!}

  union∪[A] : {S : ℙ (ℙ X)}{A : ℙ X} → union (S ∪ [ A ]) ≡ (union S) ∪ A
  union∪[A] {S = S} {A = A} = union∪ ∙ (λ i → (union S) ∪ union[A] {A = A} i)


  {-

    Finiteness of Subset

  -}

  -- Finite subset

  data isFinSubset {ℓ : Level}{X : Type ℓ} : ℙ X → Type ℓ where
    isfin∅   : isFinSubset ∅
    isfinsuc : (x : X){A : ℙ X} → isFinSubset A → isFinSubset (A ∪ [ x ])

  isFinSubset∪ : {A B : ℙ X} → isFinSubset A → isFinSubset B → isFinSubset (A ∪ B)
  isFinSubset∪ p isfin∅ = subst isFinSubset (sym (∪-rUnit _)) p
  isFinSubset∪ p (isfinsuc y finB) =
    subst isFinSubset (sym (∪-Assoc _ _ _)) (isfinsuc y (isFinSubset∪ p finB))
