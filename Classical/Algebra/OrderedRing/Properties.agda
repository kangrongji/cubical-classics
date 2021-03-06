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
open import Cubical.Data.Nat using (โ ; zero ; suc)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection
open import Cubical.Relation.Nullary

open import Classical.Algebra.OrderedRing.Base

private
  variable
    โ โ' : Level


private
  module Helpers {โ : Level}(๐ก : CommRing โ) where
    open CommRingStr (๐ก .snd)

    helper1 : (x : ๐ก .fst) โ x โก (x - 0r)
    helper1 = solve ๐ก

    helper2 : (x y : ๐ก .fst) โ x - y โก - (y - x)
    helper2 = solve ๐ก

    helper3 : (x y z : ๐ก .fst) โ (z - y) + (y - x) โก z - x
    helper3 = solve ๐ก

    helper4 : (x y : ๐ก .fst) โ (y - x) + x โก y
    helper4 = solve ๐ก

    helper5 : (x y z w : ๐ก .fst) โ (y - x) + (w - z) โก (y + w) - (x + z)
    helper5 = solve ๐ก

    helper6 : (x y : ๐ก .fst) โ y - x โก ((- x) - (- y))
    helper6 = solve ๐ก

    helper7 : (x y : ๐ก .fst) โ x ยท (- y) โก - (x ยท y)
    helper7 = solve ๐ก

    helper8 : (x y : ๐ก .fst) โ (- x) ยท (- y) โก x ยท y
    helper8 = solve ๐ก

    helper9 : (x y z : ๐ก .fst) โ (x - 0r) ยท (z - y) โก (x ยท z) - (x ยท y)
    helper9 = solve ๐ก

    helper10 : (x y z : ๐ก .fst) โ (z - y) ยท (x - 0r) โก (z ยท x) - (y ยท x)
    helper10 = solve ๐ก

    helper11 : (x y : ๐ก .fst) โ - ((- x) ยท y) โก x ยท y
    helper11 = solve ๐ก

    helper12 : (x y z : ๐ก .fst) โ y - x โก (y + z) - (x + z)
    helper12 = solve ๐ก

    helper13 : (x y z : ๐ก .fst) โ y - x โก (z + y) - (z + x)
    helper13 = solve ๐ก

    helper14 : (x y : ๐ก .fst) โ x โก (y + x) - y
    helper14 = solve ๐ก

    helper15 : (x y : ๐ก .fst) โ (x - 0r) ยท (y - 1r) โก (x ยท y) - x
    helper15 = solve ๐ก

    helper16 : 1r - 0r โก 1r
    helper16 = solve ๐ก

    helper17 : (n q : ๐ก .fst) โ (1r + n) ยท q โก (n ยท q) + q
    helper17 = solve ๐ก

    helper18 : (x : ๐ก .fst) โ - (1r + x) โก - 1r - x
    helper18 = solve ๐ก

    helper19 : (x y : ๐ก .fst) โ (x - y) + y โก x
    helper19 = solve ๐ก

    helper20 : (x y : ๐ก .fst) โ (x + y) - y โก x
    helper20 = solve ๐ก


module OrderedRingStr (๐ก : OrderedRing โ โ') where

  private
    R = ๐ก .fst .fst

  open RingTheory (CommRingโRing (๐ก .fst))
  open CommRingStr   (๐ก .fst .snd)
  open OrderStrOnCommRing (๐ก .snd)

  open Helpers (๐ก .fst)


  private
    isSetR = is-set

    variable
      x y z w : R


  {-

    Strict Ordering

  -}

  _>_ : R โ R โ Type โ'
  x > y = (x - y) >0

  _<_ : R โ R โ Type โ'
  x < y = y > x

  infix 4 _>_ _<_

  isProp< : {x y : R} โ isProp (x < y)
  isProp< {x = x} {y = y} = isProp>0 (y - x)

  >0โก>0r : (x : R) โ (x >0) โก (x > 0r)
  >0โก>0r x i = (helper1 x i) >0


  <-asym : x < y โ x > y โ โฅ
  <-asym {x = x} {y = y} x<y x>y = >0-asym (y - x) x<y (subst (_>0) (helper2 x y) x>y)

  <-arefl : x < y โ x โก y โ โฅ
  <-arefl {x = x} {y = y} x<y xโกy = <-asym {x = x} {y = y} x<y (transport (ฮป i โ xโกy i < xโกy (~ i)) x<y)

  >-arefl : x > y โ x โก y โ โฅ
  >-arefl x>y xโกy = <-arefl x>y (sym xโกy)

  <-trans : x < y โ y < z โ x < z
  <-trans {x = x} {y = y} {z = z} x<y y<z = subst (_>0) (helper3 x y z) (>0-+ (z - y) (y - x) y<z x<y)


  data Trichotomy (x y : R) : Type (โ-max โ โ') where
    lt : x < y โ Trichotomy x y
    eq : x โก y โ Trichotomy x y
    gt : x > y โ Trichotomy x y

  isPropTrichotomy : (x y : R) โ isProp (Trichotomy x y)
  isPropTrichotomy x y (lt x<y) (lt x<y') i = lt (isProp< x<y x<y' i)
  isPropTrichotomy x y (eq xโกy) (eq xโกy') i = eq (isSetR _ _ xโกy xโกy' i)
  isPropTrichotomy x y (gt x>y) (gt x>y') i = gt (isProp< x>y x>y' i)
  isPropTrichotomy x y (lt x<y) (eq xโกy) = Empty.rec (<-arefl x<y xโกy)
  isPropTrichotomy x y (lt x<y) (gt x>y) = Empty.rec (<-asym x<y x>y)
  isPropTrichotomy x y (gt x>y) (eq xโกy) = Empty.rec (<-arefl x>y (sym xโกy))
  isPropTrichotomy x y (gt x>y) (lt x<y) = Empty.rec (<-asym x<y x>y)
  isPropTrichotomy x y (eq xโกy) (lt x<y) = Empty.rec (<-arefl x<y xโกy)
  isPropTrichotomy x y (eq xโกy) (gt x>y) = Empty.rec (<-arefl x>y (sym xโกy))

  trichotomy : (x y : R) โ Trichotomy x y
  trichotomy x y with trichotomy>0 (y - x)
  ... | lt x<y = gt (subst (_>0) (sym (helper2 x y)) x<y)
  ... | eq xโกy = eq (sym (+IdL _) โ (ฮป i โ xโกy (~ i) + x) โ helper4 x y)
  ... | gt x>y = lt x>y

  dec< : (x y : R) โ Dec (x < y)
  dec< x y with trichotomy x y
  ... | lt x<y = yes x<y
  ... | eq xโกy = no (ฮป p โ <-arefl p xโกy)
  ... | gt x>y = no (ฮป p โ <-asym  p x>y)


  +-Pres< : x < y โ z < w โ x + z < y + w
  +-Pres< x<y z<w = subst (_>0) (helper5 _ _ _ _) (>0-+ _ _ x<y z<w)

  +-lPres< : x < y โ z + x < z + y
  +-lPres< {z = z} x<y = subst (_>0) (helper13 _ _ z) x<y

  +-rPres< : x < y โ x + z < y + z
  +-rPres< {z = z} x<y = subst (_>0) (helper12 _ _ z) x<y


  -Reverse< : x < y โ - x > - y
  -Reverse< x<y = subst (_>0) (helper6 _ _) x<y

  -lReverse< : - x < y โ x > - y
  -lReverse< {x = x} {y = y} -x<y = subst (_> - y) (-Idempotent x) (-Reverse< -x<y)

  -rReverse< : x < - y โ - x > y
  -rReverse< {x = x} {y = y} x<-y = subst (_< - x) (-Idempotent y) (-Reverse< x<-y)


  -Reverse>0 : x > 0r โ - x < 0r
  -Reverse>0 {x = x} x>0 = subst (- x <_) 0Selfinverse (-Reverse< x>0)

  -Reverse<0 : x < 0r โ - x > 0r
  -Reverse<0 {x = x} x<0 = subst (- x >_) 0Selfinverse (-Reverse< x<0)

  -Reverse->0 : - x > 0r โ x < 0r
  -Reverse->0 {x = x} -x>0 = subst (_< 0r) (-Idempotent x) (-Reverse>0 -x>0)

  -Reverse-<0 : - x < 0r โ x > 0r
  -Reverse-<0 {x = x} -x<0 = subst (_> 0r) (-Idempotent x) (-Reverse<0 -x<0)


  +-rPosโ> : x > 0r โ y + x > y
  +-rPosโ> {x = x} {y = y} x>0 = subst (y + x >_) (+IdR y) (+-lPres< {z = y} x>0)

  +-rNegโ< : x < 0r โ y + x < y
  +-rNegโ< {x = x} {y = y} x<0 = subst (_> y + x) (+IdR y) (+-lPres< {z = y} x<0)

  -rPosโ< : x > 0r โ y - x < y
  -rPosโ< x>0 = +-rNegโ< (-Reverse>0 x>0)

  -rNegโ> : x < 0r โ y - x > y
  -rNegโ> x<0 = +-rPosโ> (-Reverse<0 x<0)


  ยท-lPosPres< : x > 0r โ y < z โ x ยท y < x ยท z
  ยท-lPosPres< x>0 y<z = subst (_>0) (helper9  _ _ _) (>0-ยท _ _ x>0 y<z)

  ยท-rPosPres< : x > 0r โ y < z โ y ยท x < z ยท x
  ยท-rPosPres< x>0 y<z = subst (_>0) (helper10 _ _ _) (>0-ยท _ _ y<z x>0)

  ยท-PosPres> : x > 0r โ z > 0r โ x < y โ z < w โ x ยท z < y ยท w
  ยท-PosPres> x>0 z>0 x<y z<w = <-trans (ยท-rPosPres< z>0 x<y) (ยท-lPosPres< (<-trans x>0 x<y) z<w)


  +-Pres>0 : x > 0r โ y > 0r โ x + y > 0r
  +-Pres>0 {x = x} {y = y} x>0 y>0 = subst (x + y >_) (+IdR _) (+-Pres< x>0 y>0)

  +-Pres<0 : x < 0r โ y < 0r โ x + y < 0r
  +-Pres<0 {x = x} {y = y} x<0 y<0 = subst (x + y <_) (+IdR _) (+-Pres< x<0 y<0)

  ยท-Pres>0 : x > 0r โ y > 0r โ x ยท y > 0r
  ยท-Pres>0 {x = x} {y = y} = transport (ฮป i โ >0โก>0r x i โ >0โก>0r y i โ >0โก>0r (x ยท y) i) (>0-ยท x y)


  >โDiff>0 : x > y โ x - y > 0r
  >โDiff>0 x>y = transport (>0โก>0r _) x>y

  <โDiff<0 : x < y โ x - y < 0r
  <โDiff<0 x<y = subst (_< 0r) (sym (helper2 _ _)) (-Reverse>0 (transport (>0โก>0r _) x<y))

  Diff>0โ> : x - y > 0r โ x > y
  Diff>0โ> x-y>0 = transport (sym (>0โก>0r _)) x-y>0

  Diff<0โ< : x - y < 0r โ x < y
  Diff<0โ< x-y<0 = transport (sym (>0โก>0r _)) (subst (_> 0r) (sym (helper2 _ _)) (-Reverse<0 x-y<0))


  ยท-lNegReverse< : x < 0r โ y < z โ x ยท y > x ยท z
  ยท-lNegReverse< {x = x} {y = y} {z = z} x<0 y<z = transport (ฮป i โ helper11 x y i > helper11 x z i) -xยทy<-xยทz
    where -xยทy<-xยทz : - ((- x) ยท y) > - ((- x) ยท z)
          -xยทy<-xยทz = -Reverse< (ยท-lPosPres< (-Reverse<0 x<0) y<z)

  ยท-rNegReverse< : x < 0r โ y < z โ y ยท x > z ยท x
  ยท-rNegReverse< {x = x} {y = y} {z = z} x<0 y<z = transport (ฮป i โ ยทComm x y i > ยทComm x z i) (ยท-lNegReverse< x<0 y<z)


  ยท-rNegReverse>0 : x > 0r โ y < 0r โ x ยท y < 0r
  ยท-rNegReverse>0 {x = x} {y = y} x>0 y<0 = -Reverse->0 (subst (_> 0r) (helper7 x y) (ยท-Pres>0 x>0 (-Reverse<0 y<0)))

  ยท-lNegReverse>0 : x < 0r โ y > 0r โ x ยท y < 0r
  ยท-lNegReverse>0 {x = x} {y = y} x<0 y>0 = subst (_< 0r) (ยทComm y x) (ยท-rNegReverse>0 y>0 x<0)

  ยท-rNegReverse<0 : x < 0r โ y < 0r โ x ยท y > 0r
  ยท-rNegReverse<0 {x = x} {y = y} x>0 y<0 = subst (_> 0r) (helper8 x y) (ยท-Pres>0 (-Reverse<0 x>0) (-Reverse<0 y<0))


  ยท-rPosCancel>0 : x > 0r โ x ยท y > 0r โ y > 0r
  ยท-rPosCancel>0 {x = x} {y = y} x>0 xยทy>0 with trichotomy y 0r
  ... | lt y<0 = Empty.rec (<-asym (ยท-rNegReverse>0 x>0 y<0) xยทy>0)
  ... | eq yโก0 = Empty.rec (<-arefl xยทy>0 (sym (0RightAnnihilates x) โ (ฮป i โ x ยท yโก0 (~ i))))
  ... | gt y>0 = y>0

  ยท-rPosCancel<0 : x > 0r โ x ยท y < 0r โ y < 0r
  ยท-rPosCancel<0 {x = x} {y = y} x>0 xยทy<0 = -Reverse->0 (ยท-rPosCancel>0 x>0 (subst (_> 0r) (sym (helper7 x y)) (-Reverse<0 xยทy<0)))

  ยท-lPosCancel>0 : x > 0r โ y ยท x > 0r โ y > 0r
  ยท-lPosCancel>0 {x = x} {y = y} x>0 yยทx>0 = ยท-rPosCancel>0 x>0 (subst (_> 0r) (ยทComm y x) yยทx>0)

  ยท-lPosCancel<0 : x > 0r โ y ยท x < 0r โ y < 0r
  ยท-lPosCancel<0 {x = x} {y = y} x>0 yยทx<0 = ยท-rPosCancel<0 x>0 (subst (_< 0r) (ยทComm y x) yยทx<0)


  ยท-rPosCancel< : x > 0r โ x ยท y < x ยท z โ y < z
  ยท-rPosCancel< {x = x} {y = y} {z = z} x>0 xยทy<xยทz with trichotomy y z
  ... | lt y<z = y<z
  ... | eq yโกz = Empty.rec (<-arefl xยทy<xยทz (ฮป i โ x ยท yโกz i))
  ... | gt y>z = Empty.rec (<-asym (ยท-lPosPres< x>0 y>z) xยทy<xยทz)


  ยท-Posยท>1โ> : x > 0r โ y > 1r โ x ยท y > x
  ยท-Posยท>1โ> x>0 y>1 = subst (_>0) (helper15 _ _) (>0-ยท _ _ x>0 y>1)


  +-MoveLToR< : x + y < z โ x < z - y
  +-MoveLToR< {x = x} {y = y} {z = z} x+y<z = subst (_< z - y) (helper20 x y) (+-rPres< x+y<z)

  +-MoveRToL< : z < x + y โ z - y < x
  +-MoveRToL< {z = z} {x = x} {y = y} x+y>z = subst (_> z - y) (helper20 x y) (+-rPres< x+y>z)

  +-MoveLToR<' : x + y < z โ y < z - x
  +-MoveLToR<' {x = x} {y = y} {z = z} x+y<z = +-MoveLToR< (subst (_< z) (+Comm x y) x+y<z)

  +-MoveRToL<' : z < x + y โ z - x < y
  +-MoveRToL<' {z = z} {x = x} {y = y} x+y>z = +-MoveRToL< (subst (_> z) (+Comm x y) x+y>z)

  -MoveLToR< : x - y < z โ x < z + y
  -MoveLToR< {x = x} {y = y} {z = z} x-y<z = subst (x <_) (ฮป i โ z + -Idempotent y i) (+-MoveLToR< x-y<z)

  -MoveRToL< : z < x - y โ z + y < x
  -MoveRToL< {z = z} {x = x} {y = y} x-y>z = subst (x >_) (ฮป i โ z + -Idempotent y i) (+-MoveRToL< x-y>z)

  -MoveLToR<' : x - y < z โ x < y + z
  -MoveLToR<' {x = x} x-y<z = subst (x <_) (+Comm _ _) (-MoveLToR< x-y<z)

  -MoveRToL<' : z < x - y โ y + z < x
  -MoveRToL<' {x = x} x-y>z = subst (x >_) (+Comm _ _) (-MoveRToL< x-y>z)


  {-

    Non-strict Ordering

  -}

  _โค_ : R โ R โ Type (โ-max โ โ')
  x โค y = (x < y) โ (x โก y)

  _โฅ_ : R โ R โ Type (โ-max โ โ')
  x โฅ y = y โค x

  infix 4 _โฅ_ _โค_

  isPropโค : isProp (x โค y)
  isPropโค {x = x} {y = y} (inl x<y) (inl x<y') i = inl (isProp< {x} {y} x<y x<y' i)
  isPropโค (inr xโกy) (inr xโกy') i = inr (isSetR _ _ xโกy xโกy' i)
  isPropโค (inl x<y) (inr xโกy) = Empty.rec (<-arefl x<y xโกy)
  isPropโค (inr xโกy) (inl x<y) = Empty.rec (<-arefl x<y xโกy)


  โค-asym : x โค y โ x โฅ y โ x โก y
  โค-asym (inr xโกy) _ = xโกy
  โค-asym _ (inr yโกx) = sym yโกx
  โค-asym {x = x} {y = y} (inl x<y) (inl x>y) = Empty.rec (<-asym {x = x} {y = y} x<y x>y)

  โค-refl : x โก y โ x โค y
  โค-refl xโกy = inr xโกy

  โค-trans : x โค y โ y โค z โ x โค z
  โค-trans {z = z} (inr xโกy) yโคz = subst (_โค z) (sym xโกy) yโคz
  โค-trans {x = x} xโคy (inr yโกz) = subst (x โค_) yโกz xโคy
  โค-trans {x = x} {y = y} {z = z} (inl x<y) (inl y<z) = inl (<-trans {x = x} {y = y} {z = z} x<y y<z)

  โค-total : (x y : R) โ (x โค y) โ (y โค x)
  โค-total x y with trichotomy x y
  ... | lt x<y = inl (inl x<y)
  ... | eq xโกy = inl (inr xโกy)
  ... | gt x>y = inr (inl x>y)


  +-Presโฅ0 : x โฅ 0r โ y โฅ 0r โ (x + y) โฅ 0r
  +-Presโฅ0 {x = x} {y = y} (inl x>0) (inl y>0) = inl (+-Pres>0 {x = x} {y = y} x>0 y>0)
  +-Presโฅ0 {x = x} {y = y} (inr 0โกx) yโฅ0 = subst (_โฅ 0r) yโกx+y yโฅ0
    where yโกx+y : y โก x + y
          yโกx+y = sym (+IdL _) โ (ฮป i โ 0โกx i + y)
  +-Presโฅ0 {x = x} {y = y} xโฅ0 (inr 0โกy) = subst (_โฅ 0r) xโกx+y xโฅ0
    where xโกx+y : x โก x + y
          xโกx+y = sym (+IdR _) โ (ฮป i โ x + 0โกy i)

  ยท-Presโฅ0 : x โฅ 0r โ y โฅ 0r โ (x ยท y) โฅ 0r
  ยท-Presโฅ0 {x = x} {y = y} (inl x>0) (inl y>0) = inl (ยท-Pres>0 {x = x} {y = y} x>0 y>0)
  ยท-Presโฅ0 {x = x} {y = y} (inr 0โกx) yโฅ0 = inr 0โกxยทy
    where 0โกxยทy : 0r โก x ยท y
          0โกxยทy = sym (0LeftAnnihilates  y) โ (ฮป i โ 0โกx i ยท y)
  ยท-Presโฅ0 {x = x} {y = y} xโฅ0 (inr 0โกy) = inr 0โกxยทy
    where 0โกxยทy : 0r โก x ยท y
          0โกxยทy = sym (0RightAnnihilates x) โ (ฮป i โ x ยท 0โกy i)


  +-rPosโโฅ : x โฅ 0r โ y + x โฅ y
  +-rPosโโฅ (inl x>0) = inl (+-rPosโ> x>0)
  +-rPosโโฅ {y = y} (inr 0โกx) = inr (sym (+IdR y) โ (ฮป i โ y + 0โกx i))

  +-rNegโโค : x โค 0r โ y + x โค y
  +-rNegโโค (inl x<0) = inl (+-rNegโ< x<0)
  +-rNegโโค {y = y} (inr xโก0) = inr ((ฮป i โ y + xโก0 i) โ +IdR y)


  โฅโDiffโฅ0 : x โฅ y โ x - y โฅ 0r
  โฅโDiffโฅ0 (inl x>y) = inl (>โDiff>0 x>y)
  โฅโDiffโฅ0 {y = y} (inr xโกy) = inr (sym (+InvR y) โ (ฮป i โ xโกy i - y))

  โคโDiffโค0 : x โค y โ x - y โค 0r
  โคโDiffโค0 (inl x<y) = inl (<โDiff<0 x<y)
  โคโDiffโค0 {y = y} (inr yโกx) = inr ((ฮป i โ yโกx i - y) โ +InvR y)

  Diffโฅ0โโฅ : x - y โฅ 0r โ x โฅ y
  Diffโฅ0โโฅ (inl x-y>0) = inl (Diff>0โ> x-y>0)
  Diffโฅ0โโฅ {x = x} {y = y} (inr x-yโก0) = inr (sym (+IdL y) โ (ฮป i โ x-yโก0 i + y) โ helper19 x y)


  +-Presโค : x โค y โ z โค w โ x + z โค y + w
  +-Presโค xโคy zโคw = Diffโฅ0โโฅ (subst (_โฅ 0r) (helper5 _ _ _ _) (+-Presโฅ0 (โฅโDiffโฅ0 xโคy) (โฅโDiffโฅ0 zโคw)))

  +-lPresโค : x โค y โ z + x โค z + y
  +-lPresโค {z = z} xโคy = Diffโฅ0โโฅ (subst (_โฅ 0r) (helper13 _ _ z) (โฅโDiffโฅ0 xโคy))

  +-rPresโค : x โค y โ x + z โค y + z
  +-rPresโค {z = z} xโคy = Diffโฅ0โโฅ (subst (_โฅ 0r) (helper12 _ _ z) (โฅโDiffโฅ0 xโคy))


  -Reverseโค : x โค y โ - x โฅ - y
  -Reverseโค (inl x<y) = inl (-Reverse< x<y)
  -Reverseโค (inr xโกy) = inr (ฮป i โ - xโกy (~ i))

  -lReverseโค : - x โค y โ x โฅ - y
  -lReverseโค {x = x} {y = y} -xโฅy = subst (_โฅ - y) (-Idempotent x) (-Reverseโค -xโฅy)

  -rReverseโค : x โค - y โ - x โฅ y
  -rReverseโค {x = x} {y = y} xโค-y = subst (_โค - x) (-Idempotent y) (-Reverseโค xโค-y)


  ยท-lPosPresโค : x โฅ 0r โ y โค z โ x ยท y โค x ยท z
  ยท-lPosPresโค (inl 0<x) (inl y<z) = inl (ยท-lPosPres< 0<x y<z)
  ยท-lPosPresโค {y = y} {z = z} (inr 0โกx) _ =
    inr ((ฮป i โ 0โกx (~ i) ยท y) โ 0LeftAnnihilates _ โ sym (0LeftAnnihilates _) โ (ฮป i โ 0โกx i ยท z))
  ยท-lPosPresโค {x = x} _ (inr yโกz) = inr (ฮป i โ x ยท yโกz i)

  ยท-rPosPresโค : x โฅ 0r โ y โค z โ y ยท x โค z ยท x
  ยท-rPosPresโค {x = x} {y = y} {z = z} xโฅ0 yโคz = transport (ฮป i โ ยทComm x y i โค ยทComm x z i) (ยท-lPosPresโค xโฅ0 yโคz)

  ยท-PosPresโฅ : x โฅ 0r โ z โฅ 0r โ x โค y โ z โค w โ x ยท z โค y ยท w
  ยท-PosPresโฅ xโฅ0 zโฅ0 xโคy zโคw = โค-trans (ยท-rPosPresโค zโฅ0 xโคy) (ยท-lPosPresโค (โค-trans xโฅ0 xโคy) zโคw)


  {-

    Strict & Non-strict Together

  -}

  <โค-asym : x < y โ y โค x โ โฅ
  <โค-asym x<y (inl x>y) = <-asym  x<y x>y
  <โค-asym x<y (inr xโกy) = <-arefl x<y (sym xโกy)


  <โค-trans : x < y โ y โค z โ x < z
  <โค-trans x<y (inl y<z) = <-trans x<y y<z
  <โค-trans {x = x} x<y (inr yโกz) = subst (x <_) yโกz x<y

  โค<-trans : x โค y โ y < z โ x < z
  โค<-trans (inl x<y) y<z = <-trans x<y y<z
  โค<-trans {z = z} (inr xโกy) y<z = subst (_< z) (sym xโกy) y<z


  <โค-total : (x y : R) โ (x < y) โ (y โค x)
  <โค-total x y with trichotomy x y
  ... | lt x<y = inl x<y
  ... | eq xโกy = inr (inr (sym xโกy))
  ... | gt x>y = inr (inl x>y)


  ยฌ<โโฅ : ยฌ x < y โ x โฅ y
  ยฌ<โโฅ {x = x} {y = y} ยฌx<y with <โค-total x y
  ... | inl x<y = Empty.rec (ยฌx<y x<y)
  ... | inr xโฅy = xโฅy

  ยฌโคโ> : ยฌ x โค y โ x > y
  ยฌโคโ> {x = x} {y = y} ยฌxโคy with <โค-total y x
  ... | inl x>y = x>y
  ... | inr xโคy = Empty.rec (ยฌxโคy xโคy)

  โค+ยฌโกโ< : x โค y โ ยฌ x โก y โ x < y
  โค+ยฌโกโ< (inl x<y) _ = x<y
  โค+ยฌโกโ< (inr xโกy) ยฌxโกy = Empty.rec (ยฌxโกy xโกy)

  โค+ยฌ<โโก : x โค y โ ยฌ x < y โ x โก y
  โค+ยฌ<โโก (inl x<y) ยฌx<y = Empty.rec (ยฌx<y x<y)
  โค+ยฌ<โโก (inr xโกy) _ = xโกy


  ยท-PosPres>โฅ : x > 0r โ z > 0r โ x < y โ z โค w โ x ยท z < y ยท w
  ยท-PosPres>โฅ x>0 z>0 x<y (inl z<w) = ยท-PosPres> x>0 z>0 x<y z<w
  ยท-PosPres>โฅ {x = x} {z = z} {y = y} x>0 z>0 x<y (inr zโกw) =
    subst (ฮป w โ x ยท z < y ยท w) zโกw (ยท-rPosPres< z>0 x<y)

  ยท-PosPresโฅ0>0 : x โฅ 0r โ z โฅ 0r โ y > 0r โ w > 0r โ x < y โ z < w โ x ยท z < y ยท w
  ยท-PosPresโฅ0>0 (inl x>0) (inl z>0) _ _ x<y z<w = ยท-PosPres> x>0 z>0 x<y z<w
  ยท-PosPresโฅ0>0 {z = z} {y = y} {w = w} (inr 0โกx) _ y>0 w>0 _ _ =
    subst (y ยท w >_) (sym (0LeftAnnihilates _) โ (ฮป i โ 0โกx i ยท z)) (ยท-Pres>0 y>0 w>0)
  ยท-PosPresโฅ0>0 {x = x} {y = y} {w = w} _ (inr 0โกz) y>0 w>0 _ _ =
    subst (y ยท w >_) (sym (0RightAnnihilates _) โ (ฮป i โ x ยท 0โกz i)) (ยท-Pres>0 y>0 w>0)


  {-

    Ordered Ring is Integral

  -}

  ยท-lCancel : ยฌ x โก 0r โ x ยท y โก x ยท z โ y โก z
  ยท-lCancel {x = x} {y = y} {z = z} xโข0 xยทyโกxยทz with trichotomy x 0r | trichotomy y z
  ... | _      | eq yโกz = yโกz
  ... | eq xโก0 | _      = Empty.rec (xโข0 xโก0)
  ... | lt x<0 | lt y<z = Empty.rec (<-arefl (ยท-lNegReverse< x<0 y<z) (sym xยทyโกxยทz))
  ... | lt x<0 | gt y>z = Empty.rec (<-arefl (ยท-lNegReverse< x<0 y>z) xยทyโกxยทz)
  ... | gt x>0 | lt y<z = Empty.rec (<-arefl (ยท-lPosPres< x>0 y<z) xยทyโกxยทz)
  ... | gt x>0 | gt y>z = Empty.rec (<-arefl (ยท-lPosPres< x>0 y>z) (sym xยทyโกxยทz))

  ยท-rCancel : ยฌ x โก 0r โ y ยท x โก z ยท x โ y โก z
  ยท-rCancel xโข0 yยทxโกzยทx = ยท-lCancel xโข0 (ยทComm _ _ โ yยทxโกzยทx โ ยทComm _ _)


  {-

    Inclusion from Natural Numbers

  -}

  1>0 : 1r > 0r
  1>0 = subst (_>0) (sym helper16) (>0-1r)


  โโR-Pos : โ โ R
  โโR-Pos 0 = 0r
  โโR-Pos 1 = 1r
  โโR-Pos (suc (suc n)) = 1r + โโR-Pos (suc n)

  โโR-Neg : โ โ R
  โโR-Neg n = - โโR-Pos n

  โโR-PosSuc : (n : โ) โ โโR-Pos (suc n) โก 1r + โโR-Pos n
  โโR-PosSuc zero = sym (+IdR 1r)
  โโR-PosSuc (suc n) = refl

  โโR-NegSuc : (n : โ) โ โโR-Neg (suc n) โก - 1r + โโR-Neg n
  โโR-NegSuc n = (ฮป i โ - โโR-PosSuc n i) โ helper18 _


  โโR-PosSuc>0 : (n : โ) โ โโR-Pos (suc n) > 0r
  โโR-PosSuc>0 zero = 1>0
  โโR-PosSuc>0 (suc n) = +-Pres>0 1>0 (โโR-PosSuc>0 n)

  โโR-Posโฅ0 : (n : โ) โ โโR-Pos n โฅ 0r
  โโR-Posโฅ0 zero = inr refl
  โโR-Posโฅ0 (suc n) = inl (โโR-PosSuc>0 n)

  โโR-NegSuc<0 : (n : โ) โ โโR-Neg (suc n) < 0r
  โโR-NegSuc<0 n = -Reverse>0 (โโR-PosSuc>0 n)

  โโR-Negโค0 : (n : โ) โ โโR-Neg n โค 0r
  โโR-Negโค0 zero = inr 0Selfinverse
  โโR-Negโค0 (suc n) = inl (โโR-NegSuc<0 n)


  -1r : R
  -1r = - 1r

  2r : R
  2r = 1r + 1r

  -1<0 : -1r < 0r
  -1<0 = โโR-NegSuc<0 0

  2>0 : 2r > 0r
  2>0 = โโR-PosSuc>0 1


  q+1>q : {q : R} โ q + 1r > q
  q+1>q {q = q} = +-rPosโ> {x = 1r} {y = q} 1>0

  q-1<q : {q : R} โ q - 1r < q
  q-1<q {q = q} = +-rNegโ< {x = -1r} {y = q} -1<0



  {-

    Scalar multiplication by natural numbers

  -}

  _โ_ : โ โ R โ R
  n โ q = โโR-Pos n ยท q


  0โqโก0 : (q : R) โ 0 โ q โก 0r
  0โqโก0 q = 0LeftAnnihilates q

  1โqโกq : (q : R) โ 1 โ q โก q
  1โqโกq q = ยทIdL q

  sucnโqโกnโq+q : (n : โ)(q : R) โ (suc n) โ q โก (n โ q) + q
  sucnโqโกnโq+q n q = (ฮป i โ โโR-PosSuc n i ยท q) โ helper17 (โโR-Pos n) q

  sucnโq>0 : (n : โ)(q : R) โ q > 0r โ (suc n) โ q > 0r
  sucnโq>0 zero q q>0 = subst (_> 0r) (sym (1โqโกq q)) q>0
  sucnโq>0 (suc n) q q>0 = subst (_> 0r) (sym (sucnโqโกnโq+q (suc n) q))
    (+-Pres>0 {x = suc n โ q} (sucnโq>0 n q q>0) q>0)

  nโqโฅ0 : (n : โ)(q : R) โ q > 0r โ n โ q โฅ 0r
  nโqโฅ0 zero q _ = inr (sym (0โqโก0 q))
  nโqโฅ0 (suc n) q q>0 = inl (sucnโq>0 n q q>0)


  {-

    Difference and Equality

  -}

  diffโก0โxโกy : x - y โก 0r โ x โก y
  diffโก0โxโกy {y = y} x-yโก0 = sym (helper19 _ _) โ (ฮป i โ x-yโก0 i + y) โ +IdL _

  xโกyโdiffโก0 : x โก y โ x - y โก 0r
  xโกyโdiffโก0 {y = y} xโกy = (ฮป i โ xโกy i - y) โ +InvR _

  x-yโก-[y-x] : x - y โก - (y - x)
  x-yโก-[y-x] = helper2 _ _


  {-

    No Infinitesimal

  -}

  infinitesimal : x โฅ 0r โ ((ฮต : R) โ (ฮต > 0r) โ x < ฮต) โ x โก 0r
  infinitesimal {x = x} xโฅ0 โฮต>x = โค-asym (ยฌ<โโฅ ยฌx>0) xโฅ0
    where
    ยฌx>0 : ยฌ x > 0r
    ยฌx>0 x>0 = <-asym (โฮต>x x x>0) (โฮต>x x x>0)


  {-

    Minimum and Maximum of Two Elements

  -}

  min : (x y : R) โ R
  min x y with โค-total x y
  ... | inl xโคy = x
  ... | inr xโฅy = y

  minโคleft : min x y โค x
  minโคleft {x = x} {y = y} with โค-total x y
  ... | inl xโคy = โค-refl refl
  ... | inr xโฅy = xโฅy

  minโคright : min x y โค y
  minโคright {x = x} {y = y} with โค-total x y
  ... | inl xโคy = xโคy
  ... | inr xโฅy = โค-refl refl


  max : (x y : R) โ R
  max x y with โค-total x y
  ... | inl xโคy = y
  ... | inr xโฅy = x

  maxโฅleft : max x y โฅ x
  maxโฅleft {x = x} {y = y} with โค-total x y
  ... | inl xโคy = xโคy
  ... | inr xโฅy = โค-refl refl

  maxโฅright : max x y โฅ y
  maxโฅright {x = x} {y = y} with โค-total x y
  ... | inl xโคy = โค-refl refl
  ... | inr xโฅy = xโฅy
