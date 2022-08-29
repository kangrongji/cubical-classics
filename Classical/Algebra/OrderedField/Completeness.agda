{-

Dedekind/MacNeille Completeness of Ordered Field

We say an ordered field is complete, as in usually understood,
if any inhabited and bounded above subset admits least upper bound.

Warning: Classically everything is well,
but in constructive setting, this condition is called MacNeille completeness,
and Dedekind completeness refers to another notion,
c.f. `https://github.com/kangrongji/cubical-classics/issues/10`.

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Completeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection hiding (K')

open import Classical.Axioms
open import Classical.Preliminary.Logic
open import Classical.Foundations.Powerset
open import Classical.Algebra.OrderedRing.Morphism
open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Morphism
open import Classical.Algebra.OrderedField.Extremum

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝒦  : OrderedField ℓ   ℓ'
    𝒦' : OrderedField ℓ'' ℓ'''

private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (b ε : 𝓡 .fst) → (b - ε) + ε ≡ b
    helper1 = solve 𝓡


module CompleteOrderedField ⦃ 🤖 : Oracle ⦄ (𝒦 : OrderedField ℓ ℓ') where

  open Oracle 🤖

  private
    K = 𝒦 .fst .fst .fst

    variable
      p q : K

  open OrderedFieldStr 𝒦

  open Extremum 𝒦
  open Supremum
  open Infimum


  {-

    The Supremum Principle/Dedekind Completeness of Real Numbers

  -}

  isComplete : Type (ℓ-max ℓ ℓ')
  isComplete = {A : ℙ K} → isInhabited A → isUpperBounded A → Supremum A

  isPropIsComplete : isProp isComplete
  isPropIsComplete = isPropImplicitΠ (λ _ → isPropΠ2 (λ _ _ → isPropSupremum _))


  isLowerComplete : Type (ℓ-max ℓ ℓ')
  isLowerComplete = {A : ℙ K} → isInhabited A → isLowerBounded A → Infimum A


  -- Equivalence of upper/lower completeness

  isComplete→isLowerComplete : isComplete → isLowerComplete
  isComplete→isLowerComplete getSup inhab bound =
    Sup→Inf _ (getSup (isInhabited- _ inhab) (isLowerBounded→isUpperBounded _ bound))

  isLowerComplete→isComplete : isLowerComplete → isComplete
  isLowerComplete→isComplete getInf inhab bound =
    Inf→Sup _ (getInf (isInhabited- _ inhab) (isUpperBounded→isLowerBounded _ bound))


  {-

    Completeness implies Archimedean-ness

  -}


  private

    module _
      (getSup : isComplete)(q ε : K)(ε>0 : ε > 0r)
      (insurmountable' : (n : ℕ) → ¬ n ⋆ ε > q)
      where

      insurmountable : (n : ℕ) → n ⋆ ε ≤ q
      insurmountable n = ¬<→≥ (insurmountable' n)

      P : K → hProp _
      P q = ∥ Σ[ n ∈ ℕ ] n ⋆ ε > q ∥₁ , squash₁

      bounded : ℙ K
      bounded = specify P

      0∈bounded : 0r ∈ bounded
      0∈bounded = Inhab→∈ P ∣ 1 , subst (_> 0r) (sym (1⋆q≡q _)) ε>0 ∣₁

      q-bound : (x : K) → x ∈ bounded → x < q
      q-bound x x∈b =
        proof _ , isProp< by do
        (n , nε>q) ← ∈→Inhab P x∈b
        return (<≤-trans nε>q (insurmountable n))

      q-bound' : (x : K) → x ∈ bounded → x ≤ q
      q-bound' x x∈b = inl (q-bound x x∈b)

      boundary : Supremum bounded
      boundary = getSup ∣ 0r , 0∈bounded ∣₁ ∣ q , q-bound' ∣₁

      module _ (p : K)(p>q-ε : boundary .sup - ε < p)(p∈A : p ∈ bounded) where

        ∥n⋆ε>p+ε∥ : ∥ Σ[ n ∈ ℕ ] n ⋆ ε > p + ε ∥₁
        ∥n⋆ε>p+ε∥ = do
          (n , n⋆ε>p) ← ∈→Inhab P p∈A
          return (suc n ,
            subst (_> p + ε) (sym (sucn⋆q≡n⋆q+q n _)) (+-rPres< {z = ε} n⋆ε>p))

        open Helpers (𝒦 .fst .fst)

        q<p+ε : p + ε > boundary .sup
        q<p+ε = subst (_< p + ε) (helper1 _ _) (+-rPres< {z = ε} p>q-ε)

        no-way' : ⊥
        no-way' = <≤-asym q<p+ε (boundary .bound _ (Inhab→∈ P ∥n⋆ε>p+ε∥))

      q-ε<sup : boundary .sup - ε < boundary .sup
      q-ε<sup = -rPos→< ε>0

      no-way : ⊥
      no-way = proof _ , isProp⊥ by do
        (p , p>q-ε , p∈A) ← <sup→∃∈ _ boundary q-ε<sup
        return (no-way' _ p>q-ε p∈A)


  -- Complete ordered field is Archimedean

  isComplete→isArchimedean∥∥ : isComplete → isArchimedean∥∥ (𝒦 .fst)
  isComplete→isArchimedean∥∥ getSup q ε ε>0 = ¬∀¬→∃ (no-way getSup q ε ε>0)

  isComplete→isArchimedean : isComplete → isArchimedean (𝒦 .fst)
  isComplete→isArchimedean getSup = isArchimedean∥∥→isArchimedean (𝒦 .fst) (isComplete→isArchimedean∥∥ getSup)


module _ ⦃ 🤖 : Oracle ⦄ where

  open CompleteOrderedField

  CompleteOrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  CompleteOrderedField ℓ ℓ' = Σ[ 𝒦 ∈ OrderedField ℓ ℓ' ] isComplete 𝒦


  module CompleteOrderedFieldStr (𝒦 : CompleteOrderedField ℓ ℓ') where

  -- TODO: Basic corollaries of completeness.


  {-

    Homomorphism between complete ordered fields

  -}

  module CompleteOrderedFieldHom (f : OrderedFieldHom 𝒦 𝒦')
    (getSup  : isComplete 𝒦 )
    (getSup' : isComplete 𝒦')
    where

    open OrderedFieldStr 𝒦
    open OrderedFieldStr 𝒦' using ()
      renaming ( _<_ to _<'_ ; _≤_ to _≤'_
               ; _>_ to _>'_ ; _≥_ to _≥'_
               ; isProp< to isProp<'
               ; Trichotomy to Trichotomy'
               ; trichotomy to trichotomy'
               ; <-asym  to <'-asym
               ; <-trans to <'-trans
               ; is-set  to is-set')
    open OrderedRingHom    f
    open OrderedRingHomStr f
    open OrderedFieldHomStr {𝒦' = 𝒦} {𝒦 = 𝒦'} f

    private
      K  = 𝒦  .fst .fst .fst
      K' = 𝒦' .fst .fst .fst
      isSetK  = is-set
      isSetK' = is-set'
      f-map = ring-hom .fst


    findBetween : isDense
    findBetween = isArchimedean→isDense (isComplete→isArchimedean _ getSup')

    open Extremum 𝒦
    open Supremum

    module _ (y : K') where

      P : K → hProp _
      P x = (f-map x <' y) , isProp<'

      bounded : ℙ K
      bounded = specify P

      bounded-inhab : isInhabited bounded
      bounded-inhab = do
        (r , fr<y) ←
          isUnbounded→isLowerUnbounded
          (isArchimedean→isUnbounded
          (isComplete→isArchimedean _ getSup')) y
        return (r , Inhab→∈ P fr<y)

      bounded-is-bounded : isUpperBounded bounded
      bounded-is-bounded = do
        (r , y<fr) ←
          isArchimedean→isUnbounded
          (isComplete→isArchimedean _ getSup') y
        return (r , λ s s∈b →
          inl (homRefl< s r (<'-trans (∈→Inhab P s∈b) y<fr)))

      boundary : Supremum bounded
      boundary = getSup bounded-inhab bounded-is-bounded

      x = boundary .sup

      fiber-path : f-map x ≡ y
      fiber-path = case-split (trichotomy' (f-map x) y)
        where
        case-split : Trichotomy' (f-map x) y → f-map x ≡ y
        case-split (eq fx≡y) = fx≡y
        case-split (lt fx<y) = Empty.rec (
          proof _ , isProp⊥ by do
          (r , fx<fr , fr<y) ← findBetween fx<y
          return (<≤-asym (homRefl< x r fx<fr) (boundary .bound r (Inhab→∈ P fr<y))))
        case-split (gt fx>y) = Empty.rec (
          proof _ , isProp⊥ by do
          (r , y<fr , fr<fx) ← findBetween fx>y
          (s , r<s , s∈b) ← <sup→∃∈ r boundary (homRefl< r x fr<fx)
          return (<'-asym (<'-trans y<fr (homPres< r s r<s)) (∈→Inhab P s∈b)))


    isEmbedding-f : isEmbedding f-map
    isEmbedding-f = injEmbedding isSetK' (λ p → homRefl≡ _ _ p)

    isSurjection-f : isSurjection f-map
    isSurjection-f y = ∣ _ , fiber-path y ∣₁

    -- Homomorphism between complete ordered fields is always an isomorphism.

    isEquiv-f : isEquiv f-map
    isEquiv-f = isEmbedding×isSurjection→isEquiv (isEmbedding-f , isSurjection-f)

    isOrderedFieldEquivComplete : isOrderedFieldEquiv {𝒦 = 𝒦} {𝒦' = 𝒦'} f
    isOrderedFieldEquivComplete = isEquiv-f


  {-

    SIP for Complete Ordered Field

  -}

  open CompleteOrderedField
  open CompleteOrderedFieldHom

  uaCompleteOrderedField : (𝒦 𝒦' : CompleteOrderedField ℓ ℓ') → OrderedFieldHom (𝒦 .fst) (𝒦' .fst) → 𝒦 ≡ 𝒦'
  uaCompleteOrderedField 𝒦 𝒦' f i .fst =
    uaOrderedField {𝒦 = 𝒦 .fst} {𝒦' = 𝒦' .fst} {f = f} (isOrderedFieldEquivComplete f (𝒦 .snd) (𝒦' .snd)) i
  uaCompleteOrderedField 𝒦 𝒦' f i .snd =
    isProp→PathP (λ i → isPropIsComplete (uaCompleteOrderedField 𝒦 𝒦' f i .fst)) (𝒦 .snd) (𝒦' .snd) i
