{-

Dedekind Completeness of Ordered Field

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Completeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection hiding (K')

open import Classical.Preliminary.Logic
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset
open import Classical.Algebra.OrderedRing.Morphism
open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Morphism

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


module CompleteOrderedField (decide : LEM) where

  open Powerset decide

  module Completeness (𝒦 : OrderedField ℓ ℓ') where

    private
      K = 𝒦 .fst .fst .fst

      variable
        p q : K

    open OrderedFieldStr 𝒦


    record Supremum (A : ℙ K) : Type (ℓ-max ℓ ℓ') where
      field
        sup : K
        bound : (r : K) → r ∈ A → r ≤ sup
        least : (b : K) → ((r : K) → r ∈ A → r ≤ b) → b ≥ sup

    open Supremum

    isPropSupremum : (A : ℙ K) → isProp (Supremum A)
    isPropSupremum A s t i .sup = ≤-asym (s .least _ (t .bound)) (t .least _ (s .bound)) i
    isPropSupremum A s t i .bound =
      isProp→PathP (λ i → isPropΠ2 (λ r _ → isProp≤ {x = r} {y = isPropSupremum A s t i .sup})) (s .bound) (t .bound) i
    isPropSupremum A s t i .least =
      isProp→PathP (λ i → isPropΠ2 (λ b _ → isProp≤ {x = isPropSupremum A s t i .sup} {y = b})) (s .least) (t .least) i


    open ClassicalLogic decide

    <sup→∃∈ : {A : ℙ K}(q : K)(boundary : Supremum A) → q < boundary .sup → ∥ Σ[ x ∈ K ] (q < x) × (x ∈ A) ∥
    <sup→∃∈ {A = A} q boundary q<sup with decide (squash {A = Σ[ x ∈ K ] (q < x) × (x ∈ A)})
    ... | yes p = p
    ... | no ¬p = Empty.rec (<≤-asym q<sup (boundary .least _ (λ r r∈A → case-split r (trichotomy q r) r∈A)))
      where
      case-split : (x : K) → Trichotomy q x → x ∈ A → x ≤ q
      case-split _ (eq q≡x) _ = inr (sym q≡x)
      case-split _ (gt q>x) _ = inl q>x
      case-split x (lt q<x) x∈A = Empty.rec (¬∃×→∀→¬ (λ _ → isProp<) (λ _ → isProp∈ A) ¬p x q<x x∈A)


    -- Boundedness of subsets

    isUpperBounded : ℙ K → Type (ℓ-max ℓ ℓ')
    isUpperBounded A = ∥ Σ[ b ∈ K ] ((r : K) → r ∈ A → r ≤ b) ∥


    -- The Supremum Principle/Dedekind Completeness of Real Numbers

    isComplete : Type (ℓ-max ℓ ℓ')
    isComplete = {A : ℙ K} → isInhabited A → isUpperBounded A → Supremum A


    private

      module _
        (getSup : isComplete)(q ε : K)(ε>0 : ε > 0r)
        (insurmountable' : (n : ℕ) → ¬ n ⋆ ε > q)
        where

        insurmountable : (n : ℕ) → n ⋆ ε ≤ q
        insurmountable n with trichotomy (n ⋆ ε) q
        ... | lt n⋆ε<q = inl n⋆ε<q
        ... | eq n⋆ε≡q = inr n⋆ε≡q
        ... | gt n⋆ε>q = Empty.rec (insurmountable' n n⋆ε>q)

        P : K → hProp _
        P q = ∥ Σ[ n ∈ ℕ ] n ⋆ ε > q ∥ , squash

        bounded : ℙ K
        bounded = specify P

        0∈bounded : 0r ∈ bounded
        0∈bounded = Inhab→∈ P ∣ 1 , subst (_> 0r) (sym (1⋆q≡q _)) ε>0 ∣

        q-bound : (x : K) → x ∈ bounded → x < q
        q-bound x x∈b = Prop.rec isProp<
          (λ (n , nε>q) → <≤-trans nε>q (insurmountable n))
          (∈→Inhab P x∈b)

        q-bound' : (x : K) → x ∈ bounded → x ≤ q
        q-bound' x x∈b = inl (q-bound x x∈b)

        boundary : Supremum bounded
        boundary = getSup ∣ 0r , 0∈bounded ∣ ∣ q , q-bound' ∣

        module _ (p : K)(p>q-ε : boundary .sup - ε < p)(p∈A : p ∈ bounded) where

          ∥n⋆ε>p+ε∥ : ∥ Σ[ n ∈ ℕ ] n ⋆ ε > p + ε ∥
          ∥n⋆ε>p+ε∥ = Prop.map
            (λ (n , n⋆ε>p) → suc n ,
              subst (_> p + ε) (sym (sucn⋆q≡n⋆q+q n _)) (+-rPres< {z = ε} n⋆ε>p))
            (∈→Inhab P p∈A)

          open Helpers (𝒦 .fst .fst)

          q<p+ε : p + ε > boundary .sup
          q<p+ε = subst (_< p + ε) (helper1 _ _) (+-rPres< {z = ε} p>q-ε)

          no-way' : ⊥
          no-way' = <≤-asym q<p+ε (boundary .bound _ (Inhab→∈ P ∥n⋆ε>p+ε∥))

        q-ε<sup : boundary .sup - ε < boundary .sup
        q-ε<sup = +-rNeg→< (-Reverse>0 ε>0)

        no-way : ⊥
        no-way = Prop.rec isProp⊥ (λ (p , p>q-ε , p∈A) → no-way' _ p>q-ε p∈A) (<sup→∃∈ _ boundary q-ε<sup)


    -- Complete ordered field is Archimedean

    isComplete→isArchimedean∥∥ : isComplete → isArchimedean∥∥ (𝒦 .fst)
    isComplete→isArchimedean∥∥ getSup q ε ε>0 = ¬∀¬→∃ (no-way getSup q ε ε>0)

    isComplete→isArchimedean : isComplete → isArchimedean (𝒦 .fst)
    isComplete→isArchimedean getSup = isArchimedean∥∥→isArchimedean (𝒦 .fst) (isComplete→isArchimedean∥∥ getSup)


  open Completeness


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
      renaming ( 0r to 0r' ; 1r to 1r'
               ; -_ to -'_ ; _+_ to _+'_
               ; 1>0 to 1>'0
               ; inv₊ to inv'₊ ; ·-lInv₊ to ·'-lInv₊
               ; _<_ to _<'_ ; _≤_ to _≤'_
               ; _>_ to _>'_ ; _≥_ to _≥'_
               ; _⋆_ to _⋆'_
               ; p>0→p⁻¹>0 to p>'0→p⁻¹>'0
               ; isProp< to isProp<'
               ; Trichotomy to Trichotomy')
    open OrderedRingHom    f
    open OrderedRingHomStr f
    open OrderedFieldHomStr {𝒦' = 𝒦} {𝒦 = 𝒦'} f

    private
      K  = 𝒦  .fst .fst .fst
      K' = 𝒦' .fst .fst .fst
      f-map = ring-hom .fst


    findBetween : isDense
    findBetween = isArchimedean→isDense (isComplete→isArchimedean _ getSup')

    open Supremum

    module _ (y : K') where

      P : K → hProp _
      P x = (f-map x <' y) , isProp<'

      bounded : ℙ K
      bounded = specify P

      boundary : Supremum _ bounded
      boundary = getSup {!!} {!!}

      x = boundary .sup

      fiber-path : f-map x ≡ y
      fiber-path = {!!}
        where
        case-split : Trichotomy' (f-map x) y → f-map x ≡ y
        case-split (eq fx≡y) = fx≡y
        case-split (lt fx<y) = {!!}
        case-split (gt fx>y) = {!!}
