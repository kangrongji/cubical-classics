{-

Morphism between Ordered Field

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Algebra.OrderedField.Morphism where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.SetQuotients as SetQuot
open import Cubical.Relation.Nullary
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection hiding (K')

open import Classical.Algebra.OrderedRing
open import Classical.Algebra.OrderedRing.Morphism
open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝒦  : OrderedField ℓ   ℓ'
    𝒦' : OrderedField ℓ'' ℓ'''

private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (a b c d b⁻¹ d⁻¹ : 𝓡 .fst)
      → (a · d + c · b) · (b⁻¹ · d⁻¹) ≡ (a · b⁻¹) · (d · d⁻¹) + (c · d⁻¹) · (b · b⁻¹)
    helper1 = solve 𝓡

    helper2 : (a c b⁻¹ d⁻¹ : 𝓡 .fst) → (a · b⁻¹) · 1r + (c · d⁻¹) · 1r ≡ a · b⁻¹ + c · d⁻¹
    helper2 = solve 𝓡

    helper3 : (a c b⁻¹ d⁻¹ : 𝓡 .fst) → (a · c) · (b⁻¹ · d⁻¹) ≡ (a · b⁻¹) · (c · d⁻¹)
    helper3 = solve 𝓡

    helper4 : (a d b⁻¹ d⁻¹ : 𝓡 .fst) → (a · b⁻¹) · (d · d⁻¹) ≡ ((a · d) · b⁻¹) · d⁻¹
    helper4 = solve 𝓡

    helper5 : (c b b⁻¹ d⁻¹ : 𝓡 .fst) → ((c · b) · b⁻¹) · d⁻¹ ≡ (c · d⁻¹) · (b · b⁻¹)
    helper5 = solve 𝓡

    helper6 : (p q : 𝓡 .fst) → p + (q - p) ≡ q
    helper6 = solve 𝓡

    helper7 : (p ε x : 𝓡 .fst) → (p + (x + ε)) - (p + x) ≡ ε
    helper7 = solve 𝓡

    helper8 : (x y a : 𝓡 .fst) → ((x - y) + a) - x ≡ a - y
    helper8 = solve 𝓡

    helper9 : (x a b : 𝓡 .fst) → ((b - a) + a) - x ≡ b - x
    helper9 = solve 𝓡


-- The homomorphism between ordered fields is just the homomorphism between their underlying ordered rings

OrderedFieldHom : (𝒦 : OrderedField ℓ ℓ')(𝒦' : OrderedField ℓ'' ℓ''') → Type _
OrderedFieldHom 𝒦 𝒦' = OrderedRingHom (𝒦 .fst) (𝒦' .fst)


{-

  Properties of ordered field homomorphism

-}

module OrderedFieldHomStr (f : OrderedFieldHom 𝒦' 𝒦) where

  open OrderedFieldStr 𝒦
  open OrderedFieldStr 𝒦' using ()
    renaming ( 0r to 0r' ; 1r to 1r'
             ; -_ to -'_ ; _+_ to _+'_
             ; 1>0 to 1>'0
             ; inv₊ to inv'₊ ; ·-lInv₊ to ·'-lInv₊
             ; _<_ to _<'_ ; _≤_ to _≤'_
             ; _>_ to _>'_ ; _≥_ to _≥'_
             ; _⋆_ to _⋆'_
             ; p>0→p⁻¹>0 to p>'0→p⁻¹>'0)
  open OrderedRingHom    f
  open OrderedRingHomStr f
  open IsRingHom (ring-hom .snd)

  private
    K  = 𝒦  .fst .fst .fst
    K' = 𝒦' .fst .fst .fst
    f-map = ring-hom .fst


  homPresInv : {x : K'} → (x>0 : x >' 0r') → f-map (inv'₊ x>0) ≡ inv₊ (homPres>0 _ x>0)
  homPresInv {x = x} x>0 = sym (·Rid _)
    ∙ (λ i → f-map (inv'₊ x>0) · ·-rInv₊ (homPres>0 _ x>0) (~ i))
    ∙ ·Assoc _ _ _
    ∙ (λ i → fx⁻¹fx≡1 i · inv₊ (homPres>0 _ x>0))
    ∙ ·Lid _
    where
    fx⁻¹fx≡1 : f-map (inv'₊ x>0) · f-map x ≡ 1r
    fx⁻¹fx≡1 = sym (pres· _ _) ∙ (λ i → f-map (·'-lInv₊ x>0 i)) ∙ pres1


  isUnbounded : Type _
  isUnbounded = (x : K) → ∥ Σ[ r ∈ K' ] x < f-map r ∥

  isDense : Type _
  isDense = {x y : K} → x < y → ∥ Σ[ r ∈ K' ] (x < f-map r) × (f-map r < y) ∥


  isArchimedean→isUnbounded : isArchimedean (𝒦 .fst) → isUnbounded
  isArchimedean→isUnbounded archimedes x =
    ∣ (helper .fst) ⋆' 1r' , subst (_> x) (sym (homPres⋆ _ _)) (helper .snd) ∣
    where
    helper : _
    helper = archimedes x (f-map 1r') (homPres>0 _ 1>'0)


  -- Unbounded in the other direction but is equivalent by using additive inverse

  isLowerUnbounded : Type _
  isLowerUnbounded = (x : K) → ∥ Σ[ r ∈ K' ] f-map r < x ∥

  isUnbounded→isLowerUnbounded : isUnbounded → isLowerUnbounded
  isUnbounded→isLowerUnbounded exceed x = Prop.map
    (λ (r , fr>-x) → -' r ,
      transport (λ i → pres- r (~ i) < -Idempotent x i) (-Reverse< fr>-x))
    (exceed (- x))

  isLowerUnbounded→isUnbounded : isLowerUnbounded → isUnbounded
  isLowerUnbounded→isUnbounded -exceed x = Prop.map
    (λ (r , fr<-x) → -' r ,
      transport (λ i → pres- r (~ i) > -Idempotent x i) (-Reverse< fr<-x))
    (-exceed (- x))


  private

    module _
      (exceed : isUnbounded) where

      -exceed : (x : K) → ∥ Σ[ r ∈ K' ] f-map r < x ∥
      -exceed = isUnbounded→isLowerUnbounded exceed

      shrink : (x : K) → x > 0r → ∥ Σ[ r ∈ K' ] (0r < f-map r) × (f-map r < x) ∥
      shrink x x>0 = Prop.map
        (λ (r , fr>x⁻¹) →
          let x⁻¹>0 : inv₊ x>0 > 0r
              x⁻¹>0 = p>0→p⁻¹>0 x>0
              r>0 : r >' 0r'
              r>0 = homRefl>0 _ (<-trans x⁻¹>0 fr>x⁻¹)
              fr>0 : f-map r > 0r
              fr>0 = homPres>0 _ r>0
              fr⁻¹<x⁻¹⁻¹ = inv-Reverse< fr>0 x⁻¹>0 fr>x⁻¹
          in  _ , homPres>0 _ (p>'0→p⁻¹>'0 r>0) ,
              transport (λ i → homPresInv r>0 (~ i) < inv₊Idem x>0 i) fr⁻¹<x⁻¹⁻¹)
        (exceed (inv₊ x>0))


    module _
      (archimedes : isArchimedean (𝒦 .fst))
      (a b : K)(ε : K')
      (fε>0 : f-map ε > 0r)(fε<δ : f-map ε < b - a)
      (lower : K')(lower<a : f-map lower < a) where

      open import Classical.Preliminary.Nat

      step : ℕ → K
      step n = f-map lower + n ⋆ f-map ε

      P : ℕ → Type _
      P n = step n > a

      isPropP : (n : ℕ) → isProp (P n)
      isPropP _ = isProp<

      decP : (n : ℕ) → Dec (P n)
      decP n = dec< _ _

      ¬P0 : ¬ P zero
      ¬P0 = <-asym lower+0·ε<a
        where
        lower+0·ε<a : step 0 < a
        lower+0·ε<a = subst (_< a) (sym (+Rid (f-map lower))
          ∙ (λ i → f-map lower + 0⋆q≡0 (f-map ε) (~ i))) lower<a

      open Helpers (𝒦 .fst .fst)

      ∃Pn : ∥ Σ[ n ∈ ℕ ] P n ∥
      ∃Pn =
        let (n , n·ε>a-lower) =
              archimedes (a - f-map lower) (f-map ε) fε>0
            lower+n·ε>a : step n > a
            lower+n·ε>a = subst (step n >_)
              (helper6 (f-map lower) a) (+-lPres< n·ε>a-lower)
        in  ∣ n , lower+n·ε>a ∣

      interval : Σ[ n ∈ ℕ ] (¬ P n) × P (suc n)
      interval = findInterval isPropP decP ¬P0 ∃Pn

      n₀ = interval .fst

      lower+sucn⋆ε>a : step (suc n₀) > a
      lower+sucn⋆ε>a = interval .snd .snd

      diff-path : (p ε : K)(n : ℕ) → (p + (suc n) ⋆ ε) - (p + n ⋆ ε) ≡ ε
      diff-path p ε n = (λ i → (p + sucn⋆q≡n⋆q+q n ε i) - (p + n ⋆ ε)) ∙ helper7 _ _ _

      b-sucn>a-n : b - step (suc n₀) > a - step n₀
      b-sucn>a-n = transport (λ i → helper8 (step (suc n₀)) (step n₀) a i < helper9 (step (suc n₀)) a b i) -<-
        where
        diff>b-a : step (suc n₀) - step n₀ < b - a
        diff>b-a = subst (_< b - a) (sym (diff-path _ _ _)) fε<δ
        -<- : ((step (suc n₀) - step n₀) + a) - step (suc n₀) < ((b - a) + a) - step (suc n₀)
        -<- = +-rPres< (+-rPres< diff>b-a)

      a-n≥0→b>sucn : a ≥ step n₀ → b > step (suc n₀)
      a-n≥0→b>sucn -≥- = Diff>0→> (≤<-trans (≥→Diff≥0 -≥-) b-sucn>a-n)

      b>sucn : b > step (suc n₀)
      b>sucn = case-split (trichotomy a (step n₀))
        where
        case-split : Trichotomy a (step n₀) → b > step (suc n₀)
        case-split (lt a<n) = Empty.rec (interval .snd .fst a<n)
        case-split (eq a≡n) = a-n≥0→b>sucn (inr (sym a≡n))
        case-split (gt a>n) = a-n≥0→b>sucn (inl a>n)

      in-the-image : (n : ℕ) → step n ≡ f-map (lower +' n ⋆' ε)
      in-the-image n = (λ i → f-map lower + homPres⋆ n ε (~ i)) ∙ sym (pres+ _ _)

      among-them : Σ[ r ∈ K' ] (a < f-map r) × (f-map r < b)
      among-them = lower +' (suc n₀) ⋆' ε ,
        subst (_> a) (in-the-image (suc n₀)) (interval .snd .snd) ,
        subst (_< b) (in-the-image (suc n₀)) b>sucn


  isArchimedean→isDense : isArchimedean (𝒦 .fst) → isDense
  isArchimedean→isDense archimedes {x = x} {y = y} x<y = Prop.map2
    (λ (lower , lower<a) (ε , fε>0 , fε<δ) →
      among-them archimedes x y ε fε>0 fε<δ lower lower<a)
    (-exceed (isArchimedean→isUnbounded archimedes) x)
    (shrink  (isArchimedean→isUnbounded archimedes) (y - x) (>→Diff>0 x<y))


{-

  The Canonical Map from ℚ

-}

module InclusionFromℚ (𝒦 : OrderedField ℓ ℓ') where

  open import Cubical.Data.NatPlusOne
  open import Cubical.Data.Int.MoreInts.QuoInt
    using    (ℤ)
    renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_)
  open import Cubical.HITs.Rationals.QuoQ
    using (ℚ ; ℕ₊₁→ℤ ; _∼_)
    renaming (_+_ to _+ℚ_ ; _·_ to _·ℚ_)

  open import Classical.Preliminary.QuoInt
    using    (ℤOrder)
  open import Classical.Preliminary.QuoQ
  open import Classical.Algebra.OrderedRing.Morphism
  open import Classical.Preliminary.CommRing.Instances.QuoQ
    renaming (ℚ to ℚRing)


  open OrderStrOnCommRing

  open OrderedFieldStr 𝒦
  open InclusionFromℤ (𝒦 .fst)
  open OrderedRingStr  ℤOrder using () renaming (_>_ to _>ℤ_ ; >0≡>0r to >0≡>0r-ℤ)

  private
    K = 𝒦 .fst .fst .fst
    isSetK = is-set

  open Helpers (𝒦 .fst .fst)


  ℕ₊₁→ℤ>0 : (n : ℕ₊₁) → ℕ₊₁→ℤ n >ℤ 0
  ℕ₊₁→ℤ>0 (1+ n) = transport (>0≡>0r-ℤ (ℕ₊₁→ℤ (1+ n))) _

  ℕ₊₁→R : ℕ₊₁ → K
  ℕ₊₁→R n = ℤ→R (ℕ₊₁→ℤ n)

  ℕ₊₁→R>0 : (n : ℕ₊₁) → ℕ₊₁→R n > 0r
  ℕ₊₁→R>0 n = ℤ→R-Pres>0'' (ℕ₊₁→ℤ n) (ℕ₊₁→ℤ>0 n)

  ℕ₊₁→R≢0 : (n : ℕ₊₁) → ¬ ℕ₊₁→R n ≡ 0r
  ℕ₊₁→R≢0 n = >-arefl (ℕ₊₁→R>0 n)

  ℕ₊₁→ℤ-·₊₁-comm : (m n : ℕ₊₁) → ℕ₊₁→ℤ (m ·₊₁ n) ≡ (ℕ₊₁→ℤ m) ·ℤ (ℕ₊₁→ℤ n)
  ℕ₊₁→ℤ-·₊₁-comm (1+ m) (1+ n) = refl


  private

    module _ ((a , b) : ℤ × ℕ₊₁) where

      map-helper : K
      map-helper = ℤ→R a · inv (ℕ₊₁→R≢0 b)

      >0-helper' : a >ℤ 0 → map-helper > 0r
      >0-helper' a>0 = ·-Pres>0 (ℤ→R-Pres>0'' _ a>0) (p>0→p⁻¹>0 (ℕ₊₁→R>0 b))

      >0-helper : a >ℤ 0 → 𝒦 .fst .snd ._>0 map-helper
      >0-helper a>0 = transport (sym (>0≡>0r _)) (>0-helper' a>0)


    module _ ((a , b)(c , d) : ℤ × ℕ₊₁) where

      b≢0 = ℕ₊₁→R≢0 b
      d≢0 = ℕ₊₁→R≢0 d
      bd≢0 = ℕ₊₁→R≢0 (b ·₊₁ d)
      b⁻¹ = inv b≢0
      d⁻¹ = inv d≢0

      eq-helper : (r : (a , b) ∼ (c , d)) → map-helper (a , b) ≡ map-helper (c , d)
      eq-helper r = sym (·Rid _)
        ∙ (λ i → (ℤ→R a · b⁻¹) · ·-rInv d≢0 (~ i))
        ∙ helper4 _ _ _ _
        ∙ (λ i → (ℤ→R-Pres-· a (ℕ₊₁→ℤ d) (~ i) · b⁻¹) · d⁻¹)
        ∙ (λ i → (ℤ→R (r i) · b⁻¹) · d⁻¹)
        ∙ (λ i → (ℤ→R-Pres-· c (ℕ₊₁→ℤ b) i · b⁻¹) · d⁻¹)
        ∙ helper5 _ _ _ _
        ∙ (λ i → (ℤ→R c · d⁻¹) · ·-rInv b≢0 i)
        ∙ ·Rid _

      inv-path : inv (ℕ₊₁→R≢0 (b ·₊₁ d)) ≡ inv (·-≢0 b≢0 d≢0)
      inv-path i = invUniq {x≢0 = ℕ₊₁→R≢0 (b ·₊₁ d)} {y≢0 = ·-≢0 b≢0 d≢0}
        (cong ℤ→R (ℕ₊₁→ℤ-·₊₁-comm b d) ∙ ℤ→R-Pres-· _ _) i

      hom-helper : (a b c d : ℤ) → ℤ→R (a ·ℤ d +ℤ c ·ℤ b) ≡ ℤ→R a · ℤ→R d + ℤ→R c · ℤ→R b
      hom-helper a b c d = ℤ→R-Pres-+ _ _ ∙ (λ i → ℤ→R-Pres-· a d i + ℤ→R-Pres-· c b i)

      +-helper : map-helper (a ·ℤ ℕ₊₁→ℤ d +ℤ c ·ℤ ℕ₊₁→ℤ b , b ·₊₁ d) ≡ map-helper (a , b) + map-helper (c , d)
      +-helper = (λ i → hom-helper a (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ d) i · inv bd≢0)
        ∙ (λ i → (ℤ→R a · ℕ₊₁→R d + ℤ→R c · ℕ₊₁→R b) · inv-path i)
        ∙ (λ i → (ℤ→R a · ℕ₊₁→R d + ℤ→R c · ℕ₊₁→R b) · ·-Inv b≢0 d≢0 (~ i))
        ∙ helper1 _ _ _ _ _ _
        ∙ (λ i → (ℤ→R a · b⁻¹) · ·-rInv d≢0 i + (ℤ→R c · d⁻¹) · ·-rInv b≢0 i)
        ∙ helper2 _ _ _ _

      ·-helper : map-helper (a ·ℤ c , b ·₊₁ d) ≡ map-helper (a , b) · map-helper (c , d)
      ·-helper = (λ i → ℤ→R-Pres-· a c i · inv bd≢0)
        ∙ (λ i → (ℤ→R a · ℤ→R c) · inv-path i)
        ∙ (λ i → (ℤ→R a · ℤ→R c) · ·-Inv b≢0 d≢0 (~ i))
        ∙ helper3 _ _ _ _


  ℚ→K : ℚ → K
  ℚ→K =  SetQuot.elim (λ _ → isSetK) map-helper eq-helper

  ℚ→K-Pres-1 : ℚ→K 1 ≡ 1r
  ℚ→K-Pres-1 = ·-rInv _

  ℚ→K-Pres-+ : (p q : ℚ) → ℚ→K (p +ℚ q) ≡ ℚ→K p + ℚ→K q
  ℚ→K-Pres-+ = elimProp2 (λ _ _ → isSetK _ _) +-helper

  ℚ→K-Pres-· : (p q : ℚ) → ℚ→K (p ·ℚ q) ≡ ℚ→K p · ℚ→K q
  ℚ→K-Pres-· = elimProp2 (λ _ _ → isSetK _ _) ·-helper

  ℚ→K-Pres->0 : (p : ℚ) → ℚOrderedField .fst .snd ._>0 p → 𝒦 .fst .snd ._>0 (ℚ→K p)
  ℚ→K-Pres->0 = elimProp (λ _ → isPropΠ (λ _ → 𝒦 .fst .snd .isProp>0 _)) >0-helper


  {-

    (Ordered) Ring Homomorphism Instance

  -}

  isRingHomℚ→K : IsRingHom (CommRing→Ring ℚRing .snd) ℚ→K (CommRing→Ring (𝒦 .fst .fst) .snd)
  isRingHomℚ→K = makeIsRingHom ℚ→K-Pres-1 ℚ→K-Pres-+ ℚ→K-Pres-·

  ℚ→KCommRingHom : CommRingHom ℚRing (𝒦 .fst .fst)
  ℚ→KCommRingHom = _ , isRingHomℚ→K

  open OrderedRingHom

  ℚ→KOrderedRingHom : OrderedRingHom (ℚOrderedField .fst) (𝒦 .fst)
  ℚ→KOrderedRingHom .ring-hom = ℚ→KCommRingHom
  ℚ→KOrderedRingHom .pres->0  = ℚ→K-Pres->0

  ℚ→KOrderedFieldHom : OrderedFieldHom ℚOrderedField 𝒦
  ℚ→KOrderedFieldHom = ℚ→KOrderedRingHom
