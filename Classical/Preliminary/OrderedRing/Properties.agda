{-

  Properties of ordered ring

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.OrderedRing.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

open import Cubical.Relation.Nullary

open import Classical.Preliminary.OrderedRing.Base

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


module OrderedRingStr (𝓡ₒ : OrderedRing ℓ ℓ') where

  private
    𝓡 = 𝓡ₒ .fst
    R = 𝓡ₒ .fst .fst

  open RingTheory (CommRing→Ring 𝓡)
  open CommRingStr   (𝓡ₒ .fst .snd)
  open OrderStrOnCommRing (𝓡ₒ .snd)

  open Helpers 𝓡

  private
    variable
      x y z w : R

  private
    isSetR = is-set


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


  +-Pres< : x < y → z < w → x + z < y + w
  +-Pres< x<y z<w = subst (_>0) (helper5 _ _ _ _) (>0-+ _ _ x<y z<w)

  -Reverse< : x < y → - x > - y
  -Reverse< x<y = subst (_>0) (helper6 _ _) x<y


  ·-lPosPres< : x > 0r → y < z → x · y < x · z
  ·-lPosPres< x>0 y<z = subst (_>0) (helper9  _ _ _) (>0-· _ _ x>0 y<z)

  ·-rPosPres< : x > 0r → y < z → y · x < z · x
  ·-rPosPres< x>0 y<z = subst (_>0) (helper10 _ _ _) (>0-· _ _ y<z x>0)


  +-Pres>0 : x > 0r → y > 0r → (x + y) > 0r
  +-Pres>0 {x = x} {y = y} = transport (λ i → >0≡>0r x i → >0≡>0r y i → >0≡>0r (x + y) i) (>0-+ x y)

  ·-Pres>0 : x > 0r → y > 0r → (x · y) > 0r
  ·-Pres>0 {x = x} {y = y} = transport (λ i → >0≡>0r x i → >0≡>0r y i → >0≡>0r (x · y) i) (>0-· x y)


  -Reverse>0 : x > 0r → - x < 0r
  -Reverse>0 {x = x} x>0 = subst (- x <_) 0Selfinverse (-Reverse< x>0)

  -Reverse<0 : x < 0r → - x > 0r
  -Reverse<0 {x = x} x<0 = subst (- x >_) 0Selfinverse (-Reverse< x<0)

  -Reverse->0 : - x > 0r → x < 0r
  -Reverse->0 {x = x} -x>0 = subst (_< 0r) (-Idempotent x) (-Reverse>0 -x>0)

  -Reverse-<0 : - x < 0r → x > 0r
  -Reverse-<0 {x = x} -x<0 = subst (_> 0r) (-Idempotent x) (-Reverse<0 -x<0)


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
