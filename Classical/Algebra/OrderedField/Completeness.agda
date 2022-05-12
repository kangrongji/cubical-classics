{-

Dedekind Completeness of Ordered Field

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


    {-

      Supremum and Dedekind Completeness

    -}

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

    >sup→¬∈ : {A : ℙ K}(q : K)(boundary : Supremum A) → q > boundary .sup → ¬ q ∈ A
    >sup→¬∈ {A = A} q boundary q>sup q∈A with decide (isProp∈ A)
    ... | yes q∈A = <≤-asym q>sup (boundary .bound q q∈A)
    ... | no ¬q∈A = ¬q∈A q∈A

    ⊆→sup≤ : {A B : ℙ K} → A ⊆ B → (SupA : Supremum A)(SupB : Supremum B) → SupA .sup ≤ SupB .sup
    ⊆→sup≤ {A = A} {B = B} A⊆B SupA SupB = SupA .least _ (λ r r∈A → SupB .bound r (A⊆B r∈A))


    {-

      Some characterizations of supremum

    -}

    makeSupremum : (A : ℙ K) → (x : K) → x ∈ A → ((r : K) → r ∈ A → r ≤ x) → Supremum A
    makeSupremum A x x∈A x≥r∈A .sup = x
    makeSupremum A x x∈A x≥r∈A .bound = x≥r∈A
    makeSupremum A x x∈A x≥r∈A .least b b≥r∈A = b≥r∈A _ x∈A


    -- Boundedness of subsets

    isUpperBounded : ℙ K → Type (ℓ-max ℓ ℓ')
    isUpperBounded A = ∥ Σ[ b ∈ K ] ((r : K) → r ∈ A → r ≤ b) ∥


    -- The Supremum Principle/Dedekind Completeness of Real Numbers

    isComplete : Type (ℓ-max ℓ ℓ')
    isComplete = {A : ℙ K} → isInhabited A → isUpperBounded A → Supremum A

    isPropIsComplete : isProp isComplete
    isPropIsComplete = isPropImplicitΠ (λ _ → isPropΠ2 (λ _ _ → isPropSupremum _))


    {-

      Infimum

    -}

    record Infimum (A : ℙ K) : Type (ℓ-max ℓ ℓ') where
      field
        inf : K
        bound : (r : K) → r ∈ A → inf ≤ r
        most  : (b : K) → ((r : K) → r ∈ A → b ≤ r) → b ≤ inf

    open Infimum

    isPropInfimum : (A : ℙ K) → isProp (Infimum A)
    isPropInfimum A s t i .inf = ≤-asym (t .most _ (s .bound)) (s .most _ (t .bound)) i
    isPropInfimum A s t i .bound =
      isProp→PathP (λ i → isPropΠ2 (λ r _ → isProp≤ {x = isPropInfimum A s t i .inf} {y = r})) (s .bound) (t .bound) i
    isPropInfimum A s t i .most  =
      isProp→PathP (λ i → isPropΠ2 (λ b _ → isProp≤ {x = b} {y = isPropInfimum A s t i .inf})) (s .most)  (t .most)  i


    >inf→∃∈ : {A : ℙ K}(q : K)(boundary : Infimum A) → q > boundary .inf → ∥ Σ[ x ∈ K ] (x < q) × (x ∈ A) ∥
    >inf→∃∈ {A = A} q boundary q>inf with decide (squash {A = Σ[ x ∈ K ] (x < q) × (x ∈ A)})
    ... | yes p = p
    ... | no ¬p = Empty.rec (<≤-asym q>inf (boundary .most _ (λ r r∈A → case-split r (trichotomy q r) r∈A)))
      where
      case-split : (x : K) → Trichotomy q x → x ∈ A → q ≤ x
      case-split _ (eq q≡x) _ = inr q≡x
      case-split _ (lt q<x) _ = inl q<x
      case-split x (gt q>x) x∈A = Empty.rec (¬∃×→∀→¬ (λ _ → isProp<) (λ _ → isProp∈ A) ¬p x q>x x∈A)

    <inf→¬∈ : {A : ℙ K}(q : K)(boundary : Infimum A) → q < boundary .inf → ¬ q ∈ A
    <inf→¬∈ {A = A} q boundary q<inf q∈A with decide (isProp∈ A)
    ... | yes q∈A = <≤-asym q<inf (boundary .bound q q∈A)
    ... | no ¬q∈A = ¬q∈A q∈A


    isLowerBounded : ℙ K → Type (ℓ-max ℓ ℓ')
    isLowerBounded A = ∥ Σ[ b ∈ K ] ((r : K) → r ∈ A → b ≤ r) ∥

    isLowerComplete : Type (ℓ-max ℓ ℓ')
    isLowerComplete = {A : ℙ K} → isInhabited A → isLowerBounded A → Infimum A


    -- Equivalence of upper/lower completeness

    module _ (A : ℙ K) where

      -prop : K → hProp _
      -prop x = - x ∈ A , isProp∈ A

      -ℙ : ℙ K
      -ℙ = specify -prop


    x∈A→-x∈-A : (A : ℙ K){x : K} → x ∈ A → - x ∈ -ℙ A
    x∈A→-x∈-A A {x = x} x∈A = Inhab→∈ (-prop A) (subst (_∈ A) (sym (-Idempotent x)) x∈A)

    -ℙ-Idem : (A : ℙ K) → -ℙ (-ℙ A) ≡ A
    -ℙ-Idem A = bi⊆→≡ ⊆-helper ⊇helper
      where
      ⊆-helper : {x : K} → x ∈ -ℙ (-ℙ A) → x ∈ A
      ⊆-helper {x = x} x∈ =
        subst (_∈ A) (-Idempotent x) (∈→Inhab (-prop A) (∈→Inhab (-prop (-ℙ A)) x∈))

      ⊇helper : {x : K} → x ∈ A → x ∈ -ℙ (-ℙ A)
      ⊇helper {x = x} x∈ =
        Inhab→∈ (-prop (-ℙ A)) (Inhab→∈ (-prop A) (subst (_∈ A) (sym (-Idempotent x)) x∈))


    isInhabited- : (A : ℙ K) → isInhabited A → isInhabited (-ℙ A)
    isInhabited- A = Prop.map (λ (x , x∈A) → - x , x∈A→-x∈-A A x∈A)


    isUpperBounded→isLowerBounded : (A : ℙ K) → isUpperBounded A → isLowerBounded (-ℙ A)
    isUpperBounded→isLowerBounded A =
      Prop.map (λ (b , b≥r∈A) → - b , (λ r r∈-A → -lReverse≤ (b≥r∈A _ (∈→Inhab (-prop A) r∈-A))))

    isLowerBounded→isUpperBounded : (A : ℙ K) → isLowerBounded A → isUpperBounded (-ℙ A)
    isLowerBounded→isUpperBounded A =
      Prop.map (λ (b , b≤r∈A) → - b , (λ r r∈-A → -rReverse≤ (b≤r∈A _ (∈→Inhab (-prop A) r∈-A))))


    Sup→Inf- : (A : ℙ K) → Supremum A → Infimum (-ℙ A)
    Sup→Inf- A Sup .inf = - Sup .sup
    Sup→Inf- A Sup .bound r r∈-A = -lReverse≤ (Sup .bound _ (∈→Inhab (-prop A) r∈-A))
    Sup→Inf- A Sup .most  b b≤r∈-A = -rReverse≤ (Sup .least _ -b≥r∈-A)
      where
      -b≥r∈-A : (r : K) → r ∈ A → - b ≥ r
      -b≥r∈-A r r∈A = -rReverse≤ (b≤r∈-A _ (x∈A→-x∈-A A r∈A))

    Inf→Sup- : (A : ℙ K) → Infimum A → Supremum (-ℙ A)
    Inf→Sup- A Inf .sup = - Inf .inf
    Inf→Sup- A Inf .bound r r∈-A = -rReverse≤ (Inf .bound _ (∈→Inhab (-prop A) r∈-A))
    Inf→Sup- A Inf .least b b≥r∈-A = -lReverse≤ (Inf .most  _ -b≤r∈-A)
      where
      -b≤r∈-A : (r : K) → r ∈ A → - b ≤ r
      -b≤r∈-A r r∈A = -lReverse≤ (b≥r∈-A _ (x∈A→-x∈-A A r∈A))

    Sup→Inf : (A : ℙ K) → Supremum (-ℙ A) → Infimum A
    Sup→Inf A Sup = subst Infimum (-ℙ-Idem A) (Sup→Inf- _ Sup)

    Inf→Sup : (A : ℙ K) → Infimum (-ℙ A) → Supremum A
    Inf→Sup A Sup = subst Supremum (-ℙ-Idem A) (Inf→Sup- _ Sup)


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

    open Supremum

    module _ (y : K') where

      P : K → hProp _
      P x = (f-map x <' y) , isProp<'

      bounded : ℙ K
      bounded = specify P

      bounded-inhab : isInhabited bounded
      bounded-inhab = Prop.map
        (λ (r , fr<y) → r , Inhab→∈ P fr<y)
        (isUnbounded→isLowerUnbounded
        (isArchimedean→isUnbounded
        (isComplete→isArchimedean _ getSup')) y)

      bounded-is-bounded : isUpperBounded 𝒦 bounded
      bounded-is-bounded = Prop.map
        (λ (r , y<fr) → r , λ s s∈b →
          inl (homRefl< s r (<'-trans (∈→Inhab P s∈b) y<fr)))
        (isArchimedean→isUnbounded
        (isComplete→isArchimedean _ getSup') y)

      boundary : Supremum _ bounded
      boundary = getSup bounded-inhab bounded-is-bounded

      x = boundary .sup

      fiber-path : f-map x ≡ y
      fiber-path = case-split (trichotomy' (f-map x) y)
        where
        case-split : Trichotomy' (f-map x) y → f-map x ≡ y
        case-split (eq fx≡y) = fx≡y
        case-split (lt fx<y) = Empty.rec
          (Prop.rec isProp⊥
          (λ (r , fx<fr , fr<y) →
            <≤-asym (homRefl< x r fx<fr) (boundary .bound r (Inhab→∈ P fr<y)))
          (findBetween fx<y))
        case-split (gt fx>y) = Empty.rec
          (Prop.rec isProp⊥
          (λ (r , y<fr , fr<fx) → Prop.rec isProp⊥
            (λ (s , r<s , s∈b) →
              <'-asym (<'-trans y<fr (homPres< r s r<s)) (∈→Inhab P s∈b))
            (<sup→∃∈ _ r boundary (homRefl< r x fr<fx)))
          (findBetween fx>y))


    isEmbedding-f : isEmbedding f-map
    isEmbedding-f = injEmbedding isSetK isSetK' (λ p → homRefl≡ _ _ p)

    isSurjection-f : isSurjection f-map
    isSurjection-f y = ∣ _ , fiber-path y ∣

    -- Homomorphism between complete ordered fields is always an isomorphism.

    isEquiv-f : isEquiv f-map
    isEquiv-f = isEmbedding×isSurjection→isEquiv (isEmbedding-f , isSurjection-f)

    isOrderedFieldEquivComplete : isOrderedFieldEquiv {𝒦 = 𝒦} {𝒦' = 𝒦'} f
    isOrderedFieldEquivComplete = isEquiv-f


  {-

    SIP for Complete Ordered Field

  -}

  open Completeness
  open CompleteOrderedFieldHom

  uaCompleteOrderedField : (𝒦 𝒦' : CompleteOrderedField ℓ ℓ') → OrderedFieldHom (𝒦 .fst) (𝒦' .fst) → 𝒦 ≡ 𝒦'
  uaCompleteOrderedField 𝒦 𝒦' f i .fst =
    uaOrderedField {𝒦 = 𝒦 .fst} {𝒦' = 𝒦' .fst} {f = f} (isOrderedFieldEquivComplete f (𝒦 .snd) (𝒦' .snd)) i
  uaCompleteOrderedField 𝒦 𝒦' f i .snd =
    isProp→PathP (λ i → isPropIsComplete (uaCompleteOrderedField 𝒦 𝒦' f i .fst)) (𝒦 .snd) (𝒦' .snd) i
