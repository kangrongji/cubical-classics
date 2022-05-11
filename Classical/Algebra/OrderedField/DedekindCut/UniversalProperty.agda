{-

The Universal Property of Dedekind Cuts

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.DedekindCut.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset
open import Classical.Preliminary.Logic

open import Classical.Algebra.Field
open import Classical.Algebra.OrderedRing
open import Classical.Algebra.OrderedRing.Morphism
open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Morphism
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Algebra.OrderedField.DedekindCut.Base
open import Classical.Algebra.OrderedField.DedekindCut.Algebra
open import Classical.Algebra.OrderedField.DedekindCut.Order
open import Classical.Algebra.OrderedField.DedekindCut.Multiplication

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


module UniversalProperty (decide : LEM)
  (𝒦  : OrderedField ℓ ℓ')(archimedes : isArchimedean (𝒦 . fst)) where

  open CompleteOrderedField decide
  open Completeness

  module _
    (𝒦' : CompleteOrderedField ℓ' ℓ'')(f : OrderedFieldHom 𝒦 (𝒦' .fst)) where

    open Powerset decide

    open OrderedFieldStr 𝒦
    open Basics   decide 𝒦
    open Algebra  decide 𝒦 archimedes
    open Order    decide 𝒦 archimedes
    open Multiplication decide 𝒦 archimedes
    open DedekindCut

    open OrderedFieldStr (𝒦' .fst) using ()
      renaming ( _+_ to _+'_ ; -_ to -'_ ; _-_ to _-'_
               ; 0r to 0r' ; 1r to 1r'
               ; _·_ to _·'_
               ; _<_ to _<'_ ; _≤_ to _≤'_
               ; _>_ to _>'_ ; _≥_ to _≥'_
               ; isProp< to isProp<'
               ; isProp≤ to isProp≤'
               ; Trichotomy to Trichotomy'
               ; trichotomy to trichotomy'
               ; <-asym   to <'-asym
               ; <-trans  to <'-trans
               ; <≤-total to <≤-total'
               ; <≤-trans to <≤-trans'
               ; <≤-asym  to <≤-asym'
               ; ¬<→≥ to ¬<→≥'
               ; +-Pres< to +-Pres<'
               ; ·-PosPres≥0>0 to ·-PosPres≥0>0'
               ; ·-PosPres> to ·-PosPres>'
               ; <-+-Decompose to <-+-Decompose'
               ; <-·-Decompose to <-·-Decompose'
               ; >0≡>0r to >0≡>0r')
    open OrderedRingHom    f
    open OrderedRingHomStr f
    open OrderedFieldHomStr {𝒦' = 𝒦} {𝒦 = 𝒦' .fst} f
    open IsRingHom (ring-hom .snd)

    private
      K  = 𝒦  .fst .fst .fst
      K' = 𝒦' .fst .fst .fst .fst
      f-map = ring-hom .fst

    getSup = 𝒦' .snd

    open Supremum


    module _ (a : 𝕂) where

      map-prop : K' → hProp _
      map-prop x = ((q : K) → q ∈ a .upper → x <' f-map q) , isPropΠ2 (λ _ _ → isProp<')

      map-sub : ℙ K'
      map-sub = specify map-prop

      private
        map-sub-inhab : isInhabited map-sub
        map-sub-inhab = Prop.map
          (λ (q , q<r∈upper) →
            f-map q , Inhab→∈ map-prop (λ p p∈upper → homPres< _ _ (q<r∈upper _ p∈upper)))
          (a .lower-inhab)

        map-sub-bound : isUpperBounded (𝒦' .fst) map-sub
        map-sub-bound = Prop.map
          (λ (q , q∈upper) → f-map q , (λ r r∈map → inl (∈→Inhab map-prop r∈map _ q∈upper)))
          (a .upper-inhab)

      map-sup : Supremum (𝒦' .fst) map-sub
      map-sup = getSup map-sub-inhab map-sub-bound

      map-helper : K'
      map-helper = map-sup .sup


      open ClassicalLogic decide

      >sup-helper : (x : K') → ¬ x ∈ map-sub → ∥ Σ[ q ∈ K ] q ∈ a .upper × (f-map q <' x) ∥
      >sup-helper x ¬∈sub =
        Prop.rec squash
          (λ (q , q∈a , ¬sup<fq) →
            Prop.map
            (λ (r , r<q , r∈upper) →
                r , r∈upper , <≤-trans' (homPres< r q r<q) (¬<→≥' ¬sup<fq))
            (a .upper-round q q∈a))
          (¬∀→∃¬2 (λ _ _ → isProp<')
            (¬map (Inhab→∈ map-prop) ¬∈sub))

      >map-helper : (x : K') → x >' map-helper → ∥ Σ[ q ∈ K ] q ∈ a .upper × (f-map q <' x) ∥
      >map-helper x x>sup = >sup-helper x (>sup→¬∈ _ x map-sup x>sup)


      private
        ∈-helper :  ¬ map-helper ∈ map-sub → ⊥
        ∈-helper ¬∈sub = Prop.rec isProp⊥
          (λ (q , q∈a , sup>fq) →
            (Prop.rec isProp⊥
              (λ (x , fq<x , x∈sub) →
                <'-asym fq<x (∈→Inhab map-prop x∈sub q q∈a))
            (<sup→∃∈ _ _ map-sup sup>fq)))
          (>sup-helper _ ¬∈sub)

      map∈sub : map-helper ∈ map-sub
      map∈sub with decide (isProp∈ map-sub)
      ... | yes ∈sub = ∈sub
      ... | no ¬∈sub = Empty.rec (∈-helper ¬∈sub)

      map-helper< : (q : K) → q ∈ a .upper → map-helper <' f-map q
      map-helper< = ∈→Inhab map-prop map∈sub


    module _ (a : 𝕂)(b : 𝕂) where

      map-sub-⊆ : a ≥𝕂 b → map-sub b ⊆ map-sub a
      map-sub-⊆ a≥b {x = x} x∈subb =
        Inhab→∈ (map-prop a) (λ r r∈a → ∈→Inhab (map-prop b) x∈subb _ (a≥b r∈a))

      map-helper-pres≥ : a ≥𝕂 b → map-helper a ≥' map-helper b
      map-helper-pres≥ a≥b = ⊆→sup≤ _ (map-sub-⊆ a≥b) (map-sup b) (map-sup a)

      map-helper-pres> : a >𝕂 b → map-helper a >' map-helper b
      map-helper-pres> a>b with <≤-total' (map-helper b) (map-helper a)
      ... | inl fb<fa = fb<fa
      ... | inr fa≤fb = Empty.rec
        (Prop.rec isProp⊥
        (λ (q , q<r∈a , q∈b) →
          let fq∈suba : f-map q ∈ map-sub a
              fq∈suba = Inhab→∈ (map-prop a) (λ r r∈a → homPres< _ _ (q<r∈a r r∈a))
              fa≥fq : map-helper a ≥' f-map q
              fa≥fq = map-sup a .bound _ fq∈suba
              fq>fb : f-map q >' map-helper b
              fq>fb = map-helper< b _ q∈b
              fb<fa : map-helper b <' map-helper a
              fb<fa = <≤-trans' fq>fb fa≥fq
          in  <≤-asym' fb<fa fa≤fb) a>b)


    module _ (a b : 𝕂) where

      fa+fb≤ : (q : K) → q ∈ (a +𝕂 b) .upper → map-helper a +' map-helper b <' f-map q
      fa+fb≤ q q∈a+b = Prop.rec isProp<'
        (λ (s , t , s∈a , t∈b , q≡s+t) →
          subst (map-helper a +' map-helper b <'_)
            (sym (pres+ s t) ∙ (λ i → f-map (q≡s+t (~ i))))
            (+-Pres<' (map-helper< a s s∈a) (map-helper< b t t∈b)))
        (∈→Inhab (+upper a b) q∈a+b)

      fa+fb≤fa+b : map-helper a +' map-helper b ≤' map-helper (a +𝕂 b)
      fa+fb≤fa+b = map-sup (a +𝕂 b) .bound _ (Inhab→∈ (map-prop (a +𝕂 b)) fa+fb≤)

      ¬fa+fb<fa+b : ¬ map-helper a +' map-helper b <' map-helper (a +𝕂 b)
      ¬fa+fb<fa+b fa+fb<fa+b =
        let (s , t , fa<s , fb<t , fa+b≡s+t)
              = <-+-Decompose' (map-helper a) (map-helper b) _ fa+fb<fa+b
        in  Prop.rec2 isProp⊥
            (λ (p , p∈a , fp<s) (q , q∈b , fq<t) →
              let fp+q<fa+b : f-map (p + q) <' map-helper (a +𝕂 b)
                  fp+q<fa+b = transport (λ i → pres+ p q (~ i) <' fa+b≡s+t (~ i)) (+-Pres<' fp<s fq<t)
                  p+q∈a+b : (p + q) ∈ (a +𝕂 b) .upper
                  p+q∈a+b = Inhab→∈ (+upper a b) ∣ p , q , p∈a , q∈b , refl ∣
              in  <'-asym fp+q<fa+b (map-helper< (a +𝕂 b) _ p+q∈a+b))
            (>map-helper a s fa<s) (>map-helper b t fb<t)

      map-helper+ : map-helper (a +𝕂 b) ≡ map-helper a +' map-helper b
      map-helper+ = case-split (trichotomy' _ _)
        where
        case-split : Trichotomy' _ _ → _
        case-split (lt fa+b<fa+fb) = Empty.rec (<≤-asym' fa+b<fa+fb fa+fb≤fa+b)
        case-split (eq fa+b≡fa+fb) = fa+b≡fa+fb
        case-split (gt fa+b>fa+fb) = Empty.rec (¬fa+fb<fa+b fa+b>fa+fb)


    map-pres0 : map-helper 𝟘 ≡ 0r'
    map-pres0 = {!!}

    map-pres1 : map-helper 𝟙 ≡ 1r'
    map-pres1 = {!!}

    map-pres- : (a : 𝕂) → map-helper (-𝕂 a) ≡ -' map-helper a
    map-pres- = {!!}


    map-helper-pres≥0 : (a : 𝕂) → a ≥𝕂 𝟘 → map-helper a ≥' 0r'
    map-helper-pres≥0 a a≥0 = {!!}

    map-helper-pres>0 : (a : 𝕂) → a >𝕂 𝟘 → map-helper a >' 0r'
    map-helper-pres>0 a a≥0 = {!!}


    open OrderStrOnCommRing

    map-pres>0 : (a : 𝕂) → a >𝕂 𝟘 → 𝒦' .fst .fst .snd ._>0 (map-helper a)
    map-pres>0 a a>0 = transport (sym (>0≡>0r' _)) (map-helper-pres>0 a a>0)


    module _ (a b : 𝕂)(a>0 : a >𝕂 𝟘)(b>0 : b >𝕂 𝟘) where

      private
        a≥0 = <𝕂→≤𝕂 {a = 𝟘} {b = a} a>0
        b≥0 = <𝕂→≤𝕂 {a = 𝟘} {b = b} b>0
        a₊ b₊ : 𝕂₊
        a₊ = a , a≥0
        b₊ = b , b≥0

      fa·fb≤ : (q : K) → q ∈ (a₊ ·𝕂₊ b₊) .fst .upper → map-helper a ·' map-helper b <' f-map q
      fa·fb≤ q q∈a·b = Prop.rec isProp<'
        (λ (s , t , s∈a , t∈b , q≡s·t) →
          subst (map-helper a ·' map-helper b <'_)
            (sym (pres· s t) ∙ (λ i → f-map (q≡s·t (~ i))))
            (·-PosPres≥0>0' (map-helper-pres≥0 a a≥0) (map-helper-pres≥0 b b≥0)
              (homPres>0 _ (≥𝕂0+q∈upper→q>0 a a≥0 s∈a)) (homPres>0 _ (≥𝕂0+q∈upper→q>0 b b≥0 t∈b))
              (map-helper< a s s∈a) (map-helper< b t t∈b)))
        (∈→Inhab (·upper₊ a₊ b₊) q∈a·b)

      fa·fb≤fa·b : map-helper a ·' map-helper b ≤' map-helper ((a₊ ·𝕂₊ b₊) .fst)
      fa·fb≤fa·b = map-sup ((a₊ ·𝕂₊ b₊) .fst) .bound _ (Inhab→∈ (map-prop ((a₊ ·𝕂₊ b₊) .fst)) fa·fb≤)

      ¬fa·fb<fa·b : ¬ map-helper a ·' map-helper b <' map-helper ((a₊ ·𝕂₊ b₊) .fst)
      ¬fa·fb<fa·b fa·fb<fa·b =
        let (s , t , fa<s , fb<t , fa·b≡s·t)
              = <-·-Decompose' (map-helper a) (map-helper b) _
                  (map-helper-pres>0 a a>0) (map-helper-pres>0 b b>0) fa·fb<fa·b
        in  Prop.rec2 isProp⊥
            (λ (p , p∈a , fp<s) (q , q∈b , fq<t) →
              let fp·q<fa·b : f-map (p · q) <' map-helper ((a₊ ·𝕂₊ b₊) .fst)
                  fp·q<fa·b =
                    transport (λ i → pres· p q (~ i) <' fa·b≡s·t (~ i))
                      (·-PosPres>' (homPres>0 _ (≥𝕂0+q∈upper→q>0 a a≥0 p∈a))
                        (homPres>0 _ (≥𝕂0+q∈upper→q>0 b b≥0 q∈b)) fp<s fq<t)
                  p·q∈a·b : (p · q) ∈ (a₊ ·𝕂₊ b₊) .fst .upper
                  p·q∈a·b = Inhab→∈ (·upper₊ a₊ b₊) ∣ p , q , p∈a , q∈b , refl ∣
              in  <'-asym fp·q<fa·b (map-helper<  ((a₊ ·𝕂₊ b₊) .fst) _ p·q∈a·b))
            (>map-helper a s fa<s) (>map-helper b t fb<t)

      map-helper·PosPos' : map-helper ((a₊ ·𝕂₊ b₊) .fst) ≡ map-helper a ·' map-helper b
      map-helper·PosPos' = case-split (trichotomy' _ _)
        where
        case-split : Trichotomy' _ _ → _
        case-split (lt fa·b<fa·fb) = Empty.rec (<≤-asym' fa·b<fa·fb fa·fb≤fa·b)
        case-split (eq fa·b≡fa·fb) = fa·b≡fa·fb
        case-split (gt fa·b>fa·fb) = Empty.rec (¬fa·fb<fa·b fa·b>fa·fb)

      map-helper·PosPos : map-helper (a ·𝕂 b) ≡ map-helper a ·' map-helper b
      map-helper·PosPos = (λ i → map-helper (·𝕂≡·𝕂₊ a₊ b₊ i)) ∙ map-helper·PosPos'


    module _ (a b : 𝕂) where

      map-helper·Pos : a >𝕂 𝟘 → map-helper (a ·𝕂 b) ≡ map-helper a ·' map-helper b
      map-helper·Pos a>0 = case-split (trichotomy𝕂 b 𝟘)
        where
        case-split : Trichotomy𝕂 b 𝟘 → _
        case-split (gt b>0) = map-helper·PosPos a b a>0 b>0
        case-split (eq b≡0) = {!!}
        case-split (lt b<0) = {!!}

      map-helper· : map-helper (a ·𝕂 b) ≡ map-helper a ·' map-helper b
      map-helper· = case-split (trichotomy𝕂 a 𝟘)
        where
        case-split : Trichotomy𝕂 a 𝟘 → _
        case-split (gt a>0) = map-helper·Pos a>0
        case-split (eq a≡0) = {!!}
        case-split (lt a<0) = {!!}


    {-

      The Ordered Field Homomorphism Given by Universal Property

    -}

    extendedRingHom : CommRingHom 𝕂CommRing (𝒦' .fst .fst .fst)
    extendedRingHom = map-helper , makeIsRingHom map-pres1 map-helper+ map-helper·

    open OrderedRingHom

    extendedOrderedRingHom : OrderedRingHom 𝕂OrderedRing (𝒦' .fst .fst)
    extendedOrderedRingHom .ring-hom = extendedRingHom
    extendedOrderedRingHom .pres->0  = map-pres>0

    extend : OrderedFieldHom 𝕂OrderedField (𝒦' .fst)
    extend = extendedOrderedRingHom
