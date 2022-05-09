{-

  Properties of ordered ring

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Algebra.OrderedRing.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection
open import Cubical.Relation.Nullary

open import Classical.Algebra.OrderedRing.Base

private
  variable
    ℓ ℓ' : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x : 𝓡 .fst) → x ≡ (x - 0r)
    helper1 = solve 𝓡

    helper2 : (x y : 𝓡 .fst) → x - y ≡ - (y - x)
    helper2 = solve 𝓡

    helper3 : (x y z : 𝓡 .fst) → (z - y) + (y - x) ≡ z - x
    helper3 = solve 𝓡

    helper4 : (x y : 𝓡 .fst) → (y - x) + x ≡ y
    helper4 = solve 𝓡

    helper5 : (x y z w : 𝓡 .fst) → (y - x) + (w - z) ≡ (y + w) - (x + z)
    helper5 = solve 𝓡

    helper6 : (x y : 𝓡 .fst) → y - x ≡ ((- x) - (- y))
    helper6 = solve 𝓡

    helper7 : (x y : 𝓡 .fst) → x · (- y) ≡ - (x · y)
    helper7 = solve 𝓡

    helper8 : (x y : 𝓡 .fst) → (- x) · (- y) ≡ x · y
    helper8 = solve 𝓡

    helper9 : (x y z : 𝓡 .fst) → (x - 0r) · (z - y) ≡ (x · z) - (x · y)
    helper9 = solve 𝓡

    helper10 : (x y z : 𝓡 .fst) → (z - y) · (x - 0r) ≡ (z · x) - (y · x)
    helper10 = solve 𝓡

    helper11 : (x y : 𝓡 .fst) → - ((- x) · y) ≡ x · y
    helper11 = solve 𝓡

    helper12 : (x y z : 𝓡 .fst) → y - x ≡ (y + z) - (x + z)
    helper12 = solve 𝓡

    helper13 : (x y z : 𝓡 .fst) → y - x ≡ (z + y) - (z + x)
    helper13 = solve 𝓡

    helper14 : (x y : 𝓡 .fst) → x ≡ (y + x) - y
    helper14 = solve 𝓡

    helper15 : (x y : 𝓡 .fst) → (x - 0r) · (y - 1r) ≡ (x · y) - x
    helper15 = solve 𝓡

    helper16 : 1r - 0r ≡ 1r
    helper16 = solve 𝓡

    helper17 : (n q : 𝓡 .fst) → (1r + n) · q ≡ (n · q) + q
    helper17 = solve 𝓡

    helper18 : (x : 𝓡 .fst) → - (1r + x) ≡ - 1r - x
    helper18 = solve 𝓡

    helper19 : (x y : 𝓡 .fst) → (x - y) + y ≡ x
    helper19 = solve 𝓡


module OrderedRingStr (𝓡ₒ : OrderedRing ℓ ℓ') where

  private
    𝓡 = 𝓡ₒ .fst
    R = 𝓡ₒ .fst .fst

  open RingTheory (CommRing→Ring 𝓡)
  open CommRingStr   (𝓡ₒ .fst .snd)
  open OrderStrOnCommRing (𝓡ₒ .snd)

  open Helpers 𝓡


  private
    isSetR = is-set

    variable
      x y z w : R


  {-

    Strict Ordering

  -}

  _>_ : R → R → Type ℓ'
  x > y = (x - y) >0

  _<_ : R → R → Type ℓ'
  x < y = y > x

  infix 4 _>_ _<_

  isProp< : {x y : R} → isProp (x < y)
  isProp< {x = x} {y = y} = isProp>0 (y - x)

  >0≡>0r : (x : R) → (x >0) ≡ (x > 0r)
  >0≡>0r x i = (helper1 x i) >0


  <-asym : x < y → x > y → ⊥
  <-asym {x = x} {y = y} x<y x>y = >0-asym (y - x) x<y (subst (_>0) (helper2 x y) x>y)

  <-arefl : x < y → x ≡ y → ⊥
  <-arefl {x = x} {y = y} x<y x≡y = <-asym {x = x} {y = y} x<y (transport (λ i → x≡y i < x≡y (~ i)) x<y)

  >-arefl : x > y → x ≡ y → ⊥
  >-arefl x>y x≡y = <-arefl x>y (sym x≡y)

  <-trans : x < y → y < z → x < z
  <-trans {x = x} {y = y} {z = z} x<y y<z = subst (_>0) (helper3 x y z) (>0-+ (z - y) (y - x) y<z x<y)


  data Trichotomy (x y : R) : Type (ℓ-max ℓ ℓ') where
    lt : x < y → Trichotomy x y
    eq : x ≡ y → Trichotomy x y
    gt : x > y → Trichotomy x y

  isPropTrichotomy : (x y : R) → isProp (Trichotomy x y)
  isPropTrichotomy x y (lt x<y) (lt x<y') i = lt (isProp< x<y x<y' i)
  isPropTrichotomy x y (eq x≡y) (eq x≡y') i = eq (isSetR _ _ x≡y x≡y' i)
  isPropTrichotomy x y (gt x>y) (gt x>y') i = gt (isProp< x>y x>y' i)
  isPropTrichotomy x y (lt x<y) (eq x≡y) = Empty.rec (<-arefl x<y x≡y)
  isPropTrichotomy x y (lt x<y) (gt x>y) = Empty.rec (<-asym x<y x>y)
  isPropTrichotomy x y (gt x>y) (eq x≡y) = Empty.rec (<-arefl x>y (sym x≡y))
  isPropTrichotomy x y (gt x>y) (lt x<y) = Empty.rec (<-asym x<y x>y)
  isPropTrichotomy x y (eq x≡y) (lt x<y) = Empty.rec (<-arefl x<y x≡y)
  isPropTrichotomy x y (eq x≡y) (gt x>y) = Empty.rec (<-arefl x>y (sym x≡y))

  trichotomy : (x y : R) → Trichotomy x y
  trichotomy x y with trichotomy>0 (y - x)
  ... | lt x<y = gt (subst (_>0) (sym (helper2 x y)) x<y)
  ... | eq x≡y = eq (sym (+Lid _) ∙ (λ i → x≡y (~ i) + x) ∙ helper4 x y)
  ... | gt x>y = lt x>y

  dec< : (x y : R) → Dec (x < y)
  dec< x y with trichotomy x y
  ... | lt x<y = yes x<y
  ... | eq x≡y = no (λ p → <-arefl p x≡y)
  ... | gt x>y = no (λ p → <-asym  p x>y)


  +-Pres< : x < y → z < w → x + z < y + w
  +-Pres< x<y z<w = subst (_>0) (helper5 _ _ _ _) (>0-+ _ _ x<y z<w)

  +-lPres< : x < y → z + x < z + y
  +-lPres< {z = z} x<y = subst (_>0) (helper13 _ _ z) x<y

  +-rPres< : x < y → x + z < y + z
  +-rPres< {z = z} x<y = subst (_>0) (helper12 _ _ z) x<y

  -Reverse< : x < y → - x > - y
  -Reverse< x<y = subst (_>0) (helper6 _ _) x<y


  +-rPos→> : x > 0r → y + x > y
  +-rPos→> {x = x} {y = y} x>0 = subst (y + x >_) (+Rid y) (+-lPres< {z = y} x>0)

  +-rNeg→< : x < 0r → y + x < y
  +-rNeg→< {x = x} {y = y} x<0 = subst (_> y + x) (+Rid y) (+-lPres< {z = y} x<0)


  ·-lPosPres< : x > 0r → y < z → x · y < x · z
  ·-lPosPres< x>0 y<z = subst (_>0) (helper9  _ _ _) (>0-· _ _ x>0 y<z)

  ·-rPosPres< : x > 0r → y < z → y · x < z · x
  ·-rPosPres< x>0 y<z = subst (_>0) (helper10 _ _ _) (>0-· _ _ y<z x>0)

  ·-PosPres> : x > 0r → z > 0r → x < y → z < w → x · z < y · w
  ·-PosPres> x>0 z>0 x<y z<w = <-trans (·-rPosPres< z>0 x<y) (·-lPosPres< (<-trans x>0 x<y) z<w)


  +-Pres>0 : x > 0r → y > 0r → x + y > 0r
  +-Pres>0 {x = x} {y = y} = transport (λ i → >0≡>0r x i → >0≡>0r y i → >0≡>0r (x + y) i) (>0-+ x y)

  ·-Pres>0 : x > 0r → y > 0r → x · y > 0r
  ·-Pres>0 {x = x} {y = y} = transport (λ i → >0≡>0r x i → >0≡>0r y i → >0≡>0r (x · y) i) (>0-· x y)


  -Reverse>0 : x > 0r → - x < 0r
  -Reverse>0 {x = x} x>0 = subst (- x <_) 0Selfinverse (-Reverse< x>0)

  -Reverse<0 : x < 0r → - x > 0r
  -Reverse<0 {x = x} x<0 = subst (- x >_) 0Selfinverse (-Reverse< x<0)

  -Reverse->0 : - x > 0r → x < 0r
  -Reverse->0 {x = x} -x>0 = subst (_< 0r) (-Idempotent x) (-Reverse>0 -x>0)

  -Reverse-<0 : - x < 0r → x > 0r
  -Reverse-<0 {x = x} -x<0 = subst (_> 0r) (-Idempotent x) (-Reverse<0 -x<0)


  >→Diff>0 : x > y → x - y > 0r
  >→Diff>0 x>y = transport (>0≡>0r _) x>y

  <→Diff<0 : x < y → x - y < 0r
  <→Diff<0 x<y = subst (_< 0r) (sym (helper2 _ _)) (-Reverse>0 (transport (>0≡>0r _) x<y))

  Diff>0→> : x - y > 0r → x > y
  Diff>0→> x-y>0 = transport (sym (>0≡>0r _)) x-y>0

  Diff<0→< : x - y < 0r → x < y
  Diff<0→< x-y<0 = transport (sym (>0≡>0r _)) (subst (_> 0r) (sym (helper2 _ _)) (-Reverse<0 x-y<0))


  ·-lNegReverse< : x < 0r → y < z → x · y > x · z
  ·-lNegReverse< {x = x} {y = y} {z = z} x<0 y<z = transport (λ i → helper11 x y i > helper11 x z i) -x·y<-x·z
    where -x·y<-x·z : - ((- x) · y) > - ((- x) · z)
          -x·y<-x·z = -Reverse< (·-lPosPres< (-Reverse<0 x<0) y<z)

  ·-rNegReverse< : x < 0r → y < z → y · x > z · x
  ·-rNegReverse< {x = x} {y = y} {z = z} x<0 y<z = transport (λ i → ·Comm x y i > ·Comm x z i) (·-lNegReverse< x<0 y<z)


  ·-rNegReverse>0 : x > 0r → y < 0r → x · y < 0r
  ·-rNegReverse>0 {x = x} {y = y} x>0 y<0 = -Reverse->0 (subst (_> 0r) (helper7 x y) (·-Pres>0 x>0 (-Reverse<0 y<0)))

  ·-lNegReverse>0 : x < 0r → y > 0r → x · y < 0r
  ·-lNegReverse>0 {x = x} {y = y} x<0 y>0 = subst (_< 0r) (·Comm y x) (·-rNegReverse>0 y>0 x<0)

  ·-rNegReverse<0 : x < 0r → y < 0r → x · y > 0r
  ·-rNegReverse<0 {x = x} {y = y} x>0 y<0 = subst (_> 0r) (helper8 x y) (·-Pres>0 (-Reverse<0 x>0) (-Reverse<0 y<0))


  ·-rPosCancel>0 : x > 0r → x · y > 0r → y > 0r
  ·-rPosCancel>0 {x = x} {y = y} x>0 x·y>0 with trichotomy y 0r
  ... | lt y<0 = Empty.rec (<-asym (·-rNegReverse>0 x>0 y<0) x·y>0)
  ... | eq y≡0 = Empty.rec (<-arefl x·y>0 (sym (0RightAnnihilates x) ∙ (λ i → x · y≡0 (~ i))))
  ... | gt y>0 = y>0

  ·-rPosCancel<0 : x > 0r → x · y < 0r → y < 0r
  ·-rPosCancel<0 {x = x} {y = y} x>0 x·y<0 = -Reverse->0 (·-rPosCancel>0 x>0 (subst (_> 0r) (sym (helper7 x y)) (-Reverse<0 x·y<0)))

  ·-lPosCancel>0 : x > 0r → y · x > 0r → y > 0r
  ·-lPosCancel>0 {x = x} {y = y} x>0 y·x>0 = ·-rPosCancel>0 x>0 (subst (_> 0r) (·Comm y x) y·x>0)

  ·-lPosCancel<0 : x > 0r → y · x < 0r → y < 0r
  ·-lPosCancel<0 {x = x} {y = y} x>0 y·x<0 = ·-rPosCancel<0 x>0 (subst (_< 0r) (·Comm y x) y·x<0)


  ·-Pos·>1→> : x > 0r → y > 1r → x · y > x
  ·-Pos·>1→> x>0 y>1 = subst (_>0) (helper15 _ _) (>0-· _ _ x>0 y>1)


  {-

    Non-strict Ordering

  -}

  _≤_ : R → R → Type (ℓ-max ℓ ℓ')
  x ≤ y = (x < y) ⊎ (x ≡ y)

  _≥_ : R → R → Type (ℓ-max ℓ ℓ')
  x ≥ y = y ≤ x

  infix 4 _≥_ _≤_

  isProp≤ : isProp (x ≤ y)
  isProp≤ {x = x} {y = y} (inl x<y) (inl x<y') i = inl (isProp< {x} {y} x<y x<y' i)
  isProp≤ (inr x≡y) (inr x≡y') i = inr (isSetR _ _ x≡y x≡y' i)
  isProp≤ (inl x<y) (inr x≡y) = Empty.rec (<-arefl x<y x≡y)
  isProp≤ (inr x≡y) (inl x<y) = Empty.rec (<-arefl x<y x≡y)


  ≤-asym : x ≤ y → x ≥ y → x ≡ y
  ≤-asym (inr x≡y) _ = x≡y
  ≤-asym _ (inr y≡x) = sym y≡x
  ≤-asym {x = x} {y = y} (inl x<y) (inl x>y) = Empty.rec (<-asym {x = x} {y = y} x<y x>y)

  ≤-refl : x ≡ y → x ≤ y
  ≤-refl x≡y = inr x≡y

  ≤-trans : x ≤ y → y ≤ z → x ≤ z
  ≤-trans {z = z} (inr x≡y) y≤z = subst (_≤ z) (sym x≡y) y≤z
  ≤-trans {x = x} x≤y (inr y≡z) = subst (x ≤_) y≡z x≤y
  ≤-trans {x = x} {y = y} {z = z} (inl x<y) (inl y<z) = inl (<-trans {x = x} {y = y} {z = z} x<y y<z)

  ≤-total : (x ≤ y) ⊎ (y ≤ x)
  ≤-total {x = x} {y = y} with trichotomy x y
  ... | lt x<y = inl (inl x<y)
  ... | eq x≡y = inl (inr x≡y)
  ... | gt x>y = inr (inl x>y)


  +-Pres≥0 : x ≥ 0r → y ≥ 0r → (x + y) ≥ 0r
  +-Pres≥0 {x = x} {y = y} (inl x>0) (inl y>0) = inl (+-Pres>0 {x = x} {y = y} x>0 y>0)
  +-Pres≥0 {x = x} {y = y} (inr 0≡x) y≥0 = subst (_≥ 0r) y≡x+y y≥0
    where y≡x+y : y ≡ x + y
          y≡x+y = sym (+Lid _) ∙ (λ i → 0≡x i + y)
  +-Pres≥0 {x = x} {y = y} x≥0 (inr 0≡y) = subst (_≥ 0r) x≡x+y x≥0
    where x≡x+y : x ≡ x + y
          x≡x+y = sym (+Rid _) ∙ (λ i → x + 0≡y i)

  ·-Pres≥0 : x ≥ 0r → y ≥ 0r → (x · y) ≥ 0r
  ·-Pres≥0 {x = x} {y = y} (inl x>0) (inl y>0) = inl (·-Pres>0 {x = x} {y = y} x>0 y>0)
  ·-Pres≥0 {x = x} {y = y} (inr 0≡x) y≥0 = inr 0≡x·y
    where 0≡x·y : 0r ≡ x · y
          0≡x·y = sym (0LeftAnnihilates  y) ∙ (λ i → 0≡x i · y)
  ·-Pres≥0 {x = x} {y = y} x≥0 (inr 0≡y) = inr 0≡x·y
    where 0≡x·y : 0r ≡ x · y
          0≡x·y = sym (0RightAnnihilates x) ∙ (λ i → x · 0≡y i)


  +-rPos→≥ : x ≥ 0r → y + x ≥ y
  +-rPos→≥ (inl x>0) = inl (+-rPos→> x>0)
  +-rPos→≥ {y = y} (inr 0≡x) = inr (sym (+Rid y) ∙ (λ i → y + 0≡x i))

  +-rNeg→≤ : x ≤ 0r → y + x ≤ y
  +-rNeg→≤ (inl x<0) = inl (+-rNeg→< x<0)
  +-rNeg→≤ {y = y} (inr x≡0) = inr ((λ i → y + x≡0 i) ∙ +Rid y)


  ≥→Diff≥0 : x ≥ y → x - y ≥ 0r
  ≥→Diff≥0 (inl x>y) = inl (>→Diff>0 x>y)
  ≥→Diff≥0 {y = y} (inr x≡y) = inr (sym (+Rinv y) ∙ (λ i → x≡y i - y))

  Diff≥0→≥ : x - y ≥ 0r → x ≥ y
  Diff≥0→≥ (inl x-y>0) = inl (Diff>0→> x-y>0)
  Diff≥0→≥ {x = x} {y = y} (inr x-y≡0) = inr (sym (+Lid y) ∙ (λ i → x-y≡0 i + y) ∙ helper19 x y)


  {-

    Strict & Non-strict Together

  -}

  <≤-asym : x < y → y ≤ x → ⊥
  <≤-asym x<y (inl x>y) = <-asym  x<y x>y
  <≤-asym x<y (inr x≡y) = <-arefl x<y (sym x≡y)


  <≤-trans : x < y → y ≤ z → x < z
  <≤-trans x<y (inl y<z) = <-trans x<y y<z
  <≤-trans {x = x} x<y (inr y≡z) = subst (x <_) y≡z x<y

  ≤<-trans : x ≤ y → y < z → x < z
  ≤<-trans (inl x<y) y<z = <-trans x<y y<z
  ≤<-trans {z = z} (inr x≡y) y<z = subst (_< z) (sym x≡y) y<z


  ·-PosPres>≥ : x > 0r → z > 0r → x < y → z ≤ w → x · z < y · w
  ·-PosPres>≥ x>0 z>0 x<y (inl z<w) = ·-PosPres> x>0 z>0 x<y z<w
  ·-PosPres>≥ {x = x} {z = z} {y = y} x>0 z>0 x<y (inr z≡w) =
    subst (λ w → x · z < y · w) z≡w (·-rPosPres< z>0 x<y)


  {-

    Ordered Ring is Integral

  -}

  ·-lCancel : ¬ x ≡ 0r → x · y ≡ x · z → y ≡ z
  ·-lCancel {x = x} {y = y} {z = z} x≢0 x·y≡x·z with trichotomy x 0r | trichotomy y z
  ... | _      | eq y≡z = y≡z
  ... | eq x≡0 | _      = Empty.rec (x≢0 x≡0)
  ... | lt x<0 | lt y<z = Empty.rec (<-arefl (·-lNegReverse< x<0 y<z) (sym x·y≡x·z))
  ... | lt x<0 | gt y>z = Empty.rec (<-arefl (·-lNegReverse< x<0 y>z) x·y≡x·z)
  ... | gt x>0 | lt y<z = Empty.rec (<-arefl (·-lPosPres< x>0 y<z) x·y≡x·z)
  ... | gt x>0 | gt y>z = Empty.rec (<-arefl (·-lPosPres< x>0 y>z) (sym x·y≡x·z))

  ·-rCancel : ¬ x ≡ 0r → y · x ≡ z · x → y ≡ z
  ·-rCancel x≢0 y·x≡z·x = ·-lCancel x≢0 (·Comm _ _ ∙ y·x≡z·x ∙ ·Comm _ _)


  {-

    Inclusion from Natural Numbers

  -}

  1>0 : 1r > 0r
  1>0 = subst (_>0) (sym helper16) (>0-1r)


  ℕ→R-Pos : ℕ → R
  ℕ→R-Pos 0 = 0r
  ℕ→R-Pos 1 = 1r
  ℕ→R-Pos (suc (suc n)) = 1r + ℕ→R-Pos (suc n)

  ℕ→R-Neg : ℕ → R
  ℕ→R-Neg n = - ℕ→R-Pos n

  ℕ→R-PosSuc : (n : ℕ) → ℕ→R-Pos (suc n) ≡ 1r + ℕ→R-Pos n
  ℕ→R-PosSuc zero = sym (+Rid 1r)
  ℕ→R-PosSuc (suc n) = refl

  ℕ→R-NegSuc : (n : ℕ) → ℕ→R-Neg (suc n) ≡ - 1r + ℕ→R-Neg n
  ℕ→R-NegSuc n = (λ i → - ℕ→R-PosSuc n i) ∙ helper18 _


  ℕ→R-PosSuc>0 : (n : ℕ) → ℕ→R-Pos (suc n) > 0r
  ℕ→R-PosSuc>0 zero = 1>0
  ℕ→R-PosSuc>0 (suc n) = +-Pres>0 1>0 (ℕ→R-PosSuc>0 n)

  ℕ→R-Pos≥0 : (n : ℕ) → ℕ→R-Pos n ≥ 0r
  ℕ→R-Pos≥0 zero = inr refl
  ℕ→R-Pos≥0 (suc n) = inl (ℕ→R-PosSuc>0 n)

  ℕ→R-NegSuc<0 : (n : ℕ) → ℕ→R-Neg (suc n) < 0r
  ℕ→R-NegSuc<0 n = -Reverse>0 (ℕ→R-PosSuc>0 n)

  ℕ→R-Neg≤0 : (n : ℕ) → ℕ→R-Neg n ≤ 0r
  ℕ→R-Neg≤0 zero = inr 0Selfinverse
  ℕ→R-Neg≤0 (suc n) = inl (ℕ→R-NegSuc<0 n)


  -1r : R
  -1r = - 1r

  2r : R
  2r = 1r + 1r

  -1<0 : -1r < 0r
  -1<0 = ℕ→R-NegSuc<0 0

  2>0 : 2r > 0r
  2>0 = ℕ→R-PosSuc>0 1


  q+1>q : {q : R} → q + 1r > q
  q+1>q {q = q} = +-rPos→> {x = 1r} {y = q} 1>0

  q-1<q : {q : R} → q - 1r < q
  q-1<q {q = q} = +-rNeg→< {x = -1r} {y = q} -1<0



  {-

    Scalar multiplication by natural numbers

  -}

  _⋆_ : ℕ → R → R
  n ⋆ q = ℕ→R-Pos n · q


  0⋆q≡0 : (q : R) → 0 ⋆ q ≡ 0r
  0⋆q≡0 q = 0LeftAnnihilates q

  1⋆q≡q : (q : R) → 1 ⋆ q ≡ q
  1⋆q≡q q = ·Lid q

  sucn⋆q≡n⋆q+q : (n : ℕ)(q : R) → (suc n) ⋆ q ≡ (n ⋆ q) + q
  sucn⋆q≡n⋆q+q n q = (λ i → ℕ→R-PosSuc n i · q) ∙ helper17 (ℕ→R-Pos n) q

  sucn⋆q>0 : (n : ℕ)(q : R) → q > 0r → (suc n) ⋆ q > 0r
  sucn⋆q>0 zero q q>0 = subst (_> 0r) (sym (1⋆q≡q q)) q>0
  sucn⋆q>0 (suc n) q q>0 = subst (_> 0r) (sym (sucn⋆q≡n⋆q+q (suc n) q))
    (+-Pres>0 {x = suc n ⋆ q} (sucn⋆q>0 n q q>0) q>0)

  n⋆q≥0 : (n : ℕ)(q : R) → q > 0r → n ⋆ q ≥ 0r
  n⋆q≥0 zero q _ = inr (sym (0⋆q≡0 q))
  n⋆q≥0 (suc n) q q>0 = inl (sucn⋆q>0 n q q>0)
