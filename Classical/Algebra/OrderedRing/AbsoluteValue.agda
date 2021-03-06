{-

Absolute Value

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedRing.AbsoluteValue where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection
open import Cubical.Relation.Nullary

open import Classical.Algebra.OrderedRing

private
  variable
    β β' : Level


private
  module Helpers {β : Level}(π‘ : CommRing β) where
    open CommRingStr (π‘ .snd)

    helper1 : (x : π‘ .fst) β x β‘ (x - 0r)
    helper1 = solve π‘

    helper2 : (x y d : π‘ .fst) β ((x - d) + d) - y β‘ x - y
    helper2 = solve π‘

    helper3 : (x y d : π‘ .fst) β (y + d) - y β‘ d
    helper3 = solve π‘

    helper4 : (x y d : π‘ .fst) β (y + d) - y β‘ d
    helper4 = solve π‘

    helper5 : (x y : π‘ .fst) β - x - y β‘ - (x + y)
    helper5 = solve π‘

    helper6 : (x y z : π‘ .fst) β (x - y) + (y - z) β‘ x - z
    helper6 = solve π‘

    helper7 : (x d : π‘ .fst) β x β‘ (x + d) - d
    helper7 = solve π‘

    helper8 : (x y : π‘ .fst) β y - x β‘ - (x - y)
    helper8 = solve π‘

    helper9 : (x d : π‘ .fst) β (x + d) - x β‘ d
    helper9 = solve π‘


module AbsoluteValue (π‘ : OrderedRing β β') where

  private
    R = π‘ .fst .fst

  open RingTheory (CommRingβRing (π‘ .fst))
  open CommRingStr   (π‘ .fst .snd)
  open OrderedRingStr π‘

  open Helpers (π‘ .fst)


  private
    variable
      x y z d : R


  abs : R β R
  abs x with trichotomy x 0r
  ... | lt x<0 = - x
  ... | eq xβ‘0 = 0r
  ... | gt x>0 = x

  absβ₯0 : abs x β₯ 0r
  absβ₯0 {x = x} with trichotomy x 0r
  ... | lt x<0 = inl (-Reverse<0 x<0)
  ... | eq xβ‘0 = inr refl
  ... | gt x>0 = inl x>0

  absβ‘0βxβ‘0 : abs x β‘ 0r β x β‘ 0r
  absβ‘0βxβ‘0 {x = x} absβ‘0 with trichotomy x 0r
  ... | lt x<0 = sym (-Idempotent _) β (Ξ» i β - absβ‘0 i) β 0Selfinverse
  ... | eq xβ‘0 = xβ‘0
  ... | gt x>0 = absβ‘0


  x>0βabsβ‘x : x > 0r β abs x β‘ x
  x>0βabsβ‘x {x = x} x>0 with trichotomy x 0r
  ... | lt x<0 = Empty.rec (<-asym  x>0 x<0)
  ... | eq xβ‘0 = Empty.rec (<-arefl x>0 (sym xβ‘0))
  ... | gt x>0 = refl

  x<0βabsβ‘-x : x < 0r β abs x β‘ - x
  x<0βabsβ‘-x {x = x} x<0 with trichotomy x 0r
  ... | lt x<0 = refl
  ... | eq xβ‘0 = Empty.rec (<-arefl x<0 xβ‘0)
  ... | gt x>0 = Empty.rec (<-asym  x>0 x<0)

  xβ‘0βabsβ‘0 : x β‘ 0r β abs x β‘ 0r
  xβ‘0βabsβ‘0 {x = x} xβ‘0 with trichotomy x 0r
  ... | lt x<0 = Empty.rec (<-arefl x<0 xβ‘0)
  ... | eq xβ‘0 = refl
  ... | gt x>0 = Empty.rec (<-arefl x>0 (sym xβ‘0))


  xβ₯0βabsβ‘x : x β₯ 0r β abs x β‘ x
  xβ₯0βabsβ‘x {x = x} xβ₯0 with trichotomy x 0r
  ... | lt x<0 = Empty.rec (<β€-asym x<0 xβ₯0)
  ... | eq xβ‘0 = sym xβ‘0
  ... | gt x>0 = refl

  xβ€0βabsβ‘-x : x β€ 0r β abs x β‘ - x
  xβ€0βabsβ‘-x {x = x} xβ€0 with trichotomy x 0r
  ... | lt x<0 = refl
  ... | eq xβ‘0 = sym 0Selfinverse β (Ξ» i β - xβ‘0 (~ i))
  ... | gt x>0 = Empty.rec (<β€-asym x>0 xβ€0)


  absxβ‘βabs-x : abs x β‘ abs (- x)
  absxβ‘βabs-x {x = x} with trichotomy x 0r
  ... | lt x<0 = sym (x>0βabsβ‘x (-Reverse<0 x<0))
  ... | eq xβ‘0 = sym (xβ‘0βabsβ‘0 refl) β (Ξ» i β abs (0Selfinverse (~ i))) β (Ξ» i β abs (- xβ‘0 (~ i)))
  ... | gt x>0 = sym (-Idempotent _) β sym (x<0βabsβ‘-x (-Reverse>0 x>0))


  absSuppressβ€ : x β€ z β abs (x - y) < d β y < z + d
  absSuppressβ€ {x = x} {y = y} {d = d} xβ€z β£x-yβ£<d = case-split (<β€-total y x)
    where
    case-split : (x > y) β (x β€ y) β _
    case-split (inl x>y) = <-trans (<β€-trans x>y xβ€z) (+-rPosβ> (β€<-trans absβ₯0 β£x-yβ£<d))
    case-split (inr xβ€y) = <β€-trans (-MoveLToR<' y-x<d) (+-rPresβ€ xβ€z)
      where
      y-x<d : y - x < d
      y-x<d = subst (_< d) (xβ€0βabsβ‘-x (β€βDiffβ€0 xβ€y) β (sym (helper8 _ _))) β£x-yβ£<d

  absSuppressβ₯ : z β€ x β abs (x - y) < d β z - d < y
  absSuppressβ₯ {x = x} {y = y} {d = d} zβ€x β£x-yβ£<d = case-split (<β€-total x y)
    where
    case-split : (y > x) β (y β€ x) β _
    case-split (inl y>x) = <-trans (-rPosβ< (β€<-trans absβ₯0 β£x-yβ£<d)) (β€<-trans zβ€x y>x)
    case-split (inr yβ€x) = β€<-trans (+-rPresβ€ zβ€x) (+-MoveRToL< (-MoveLToR<' x-y<d))
      where
      x-y<d : x - y < d
      x-y<d = subst (_< d) (xβ₯0βabsβ‘x (β₯βDiffβ₯0 yβ€x)) β£x-yβ£<d


  absKeepSign+ : x > 0r β abs (x - y) < x β y > 0r
  absKeepSign+ {x = x} {y = y} x>0 β£x-yβ£<x with trichotomy y 0r
  ... | lt y<0 = Empty.rec (<-asym β£x-yβ£<x (subst (_> x) (sym β£x-yβ£β‘x-y) x-y>x))
    where
    x-y>x : x - y > x
    x-y>x = +-rPosβ> (-Reverse<0 y<0)
    β£x-yβ£β‘x-y : abs (x - y) β‘ x - y
    β£x-yβ£β‘x-y =  x>0βabsβ‘x (<-trans x>0 x-y>x)
  ... | eq yβ‘0 = Empty.rec (<-arefl (subst (_< x) β£x-yβ£β‘x β£x-yβ£<x) refl)
    where
    β£x-yβ£β‘x : abs (x - y) β‘ x
    β£x-yβ£β‘x = (Ξ» i β abs (x - yβ‘0 i)) β (Ξ» i β abs (helper1 x (~ i))) β x>0βabsβ‘x x>0
  ... | gt y>0 = y>0

  absKeepSign- : x < 0r β abs (x - y) < - x β y < 0r
  absKeepSign- {x = x} {y = y} x<0 β£x-yβ£<-x with trichotomy y 0r
  ... | lt y<0 = y<0
  ... | eq yβ‘0 = Empty.rec (<-arefl (subst (_< - x) β£x-yβ£β‘x β£x-yβ£<-x) refl)
    where
    β£x-yβ£β‘x : abs (x - y) β‘ - x
    β£x-yβ£β‘x = (Ξ» i β abs (x - yβ‘0 i)) β (Ξ» i β abs (helper1 x (~ i))) β x<0βabsβ‘-x x<0
  ... | gt y>0 = Empty.rec (<-asym β£x-yβ£<-x (subst (_> - x) (sym β£x-yβ£β‘-x-y) (-Reverse< x-y<x)))
    where
    x-y<x : x - y < x
    x-y<x = -rPosβ< y>0
    β£x-yβ£β‘-x-y : abs (x - y) β‘ - (x - y)
    β£x-yβ£β‘-x-y =  x<0βabsβ‘-x (<-trans x-y<x x<0)


  absInBetween : d > 0r β x - d β€ y β y β€ x β abs (x - y) β€ d
  absInBetween {d = d} {x = x} {y = y} d>0 x-dβ€y yβ€x = subst (_β€ d) x-yβ‘β£x-yβ£ x-yβ€d
    where
    x-yβ€d : x - y β€ d
    x-yβ€d = transport (Ξ» i β helper2 x y d i β€ helper3 x y d i) (+-rPresβ€ (+-rPresβ€ x-dβ€y))
    x-yβ‘β£x-yβ£ : x - y β‘ abs (x - y)
    x-yβ‘β£x-yβ£ = sym (xβ₯0βabsβ‘x (β₯βDiffβ₯0 yβ€x))

  absInBetween< : d > 0r β x - d < y β y < x β abs (x - y) < d
  absInBetween< {d = d} {x = x} {y = y} d>0 x-d<y y<x = subst (_< d) x-yβ‘β£x-yβ£ x-y<d
    where
    x-y<d : x - y < d
    x-y<d = transport (Ξ» i β helper2 x y d i < helper3 x y d i) (+-rPres< (+-rPres< x-d<y))
    x-yβ‘β£x-yβ£ : x - y β‘ abs (x - y)
    x-yβ‘β£x-yβ£ = sym (x>0βabsβ‘x (>βDiff>0 y<x))

  absInBetween<' : d > 0r β x < y β y < x + d β abs (x - y) < d
  absInBetween<' {d = d} {x = x} {y = y} d>0 x<y y<x+d = subst (_< d) x-yβ‘β£x-yβ£ x-y<d
    where
    x-y<d : y - x < d
    x-y<d = transport (Ξ» i β y - x < helper9 x d i) (+-rPres< y<x+d)
    x-yβ‘β£x-yβ£ : y - x β‘ abs (x - y)
    x-yβ‘β£x-yβ£ = helper8 _ _ β sym (x<0βabsβ‘-x (<βDiff<0 x<y))

  absInOpenInterval : d > 0r β x - d < y β y < x + d β abs (x - y) < d
  absInOpenInterval {d = d} {x = x} {y = y} d>0 x-d<y y<x+d = case-split (trichotomy x y)
    where
    case-split : Trichotomy x y β _
    case-split (gt x>y) = absInBetween<  d>0 x-d<y x>y
    case-split (lt x<y) = absInBetween<' d>0 x<y y<x+d
    case-split (eq xβ‘y) = subst (_< d) (sym (xβ‘0βabsβ‘0 (xβ‘yβdiffβ‘0 xβ‘y))) d>0

  absInBetween<β€ : d > 0r β x - d < y β y β€ x β abs (x - y) < d
  absInBetween<β€ d>0 x-d<y yβ€x = absInOpenInterval d>0 x-d<y (β€<-trans yβ€x (+-rPosβ> d>0))


  private
    absIneq+Pos : x β₯ 0r β abs x + abs y β₯ abs (x + y)
    absIneq+Pos {x = x} {y = y} (inr 0β‘x) =
      transport (Ξ» i β left (~ i) β₯ right (~ i)) (inr refl)
      where
      left : abs x + abs y β‘ abs y
      left = (Ξ» i β xβ‘0βabsβ‘0 (sym 0β‘x) i + abs y) β +IdL _
      right : abs (x + y) β‘ abs y
      right = cong abs ((Ξ» i β 0β‘x (~ i) + y) β +IdL _)
    absIneq+Pos {x = x} {y = y} (inl x>0) = case-split (trichotomy y 0r) (trichotomy (x + y) 0r)
      where
      case-split : Trichotomy y 0r β Trichotomy (x + y) 0r β _
      case-split (eq yβ‘0) _ =
        transport (Ξ» i β left (~ i) β₯ right (~ i)) (inr refl)
        where
        left : abs x + abs y β‘ abs x
        left = (Ξ» i β abs x + xβ‘0βabsβ‘0 yβ‘0 i) β +IdR _
        right : abs (x + y) β‘ abs x
        right = cong abs ((Ξ» i β x + yβ‘0 i) β +IdR _)
      case-split (gt y>0) _ =
        transport (Ξ» i β x>0βabsβ‘x x>0 (~ i) + x>0βabsβ‘x y>0 (~ i) β₯ x>0βabsβ‘x ineq (~ i)) (inr refl)
        where
        ineq : x + y > 0r
        ineq = +-Pres>0 x>0 y>0
      case-split (lt y<0) (lt x+y<0) =
        transport (Ξ» i β x>0βabsβ‘x x>0 (~ i) + x<0βabsβ‘-x y<0 (~ i) β₯ x<0βabsβ‘-x x+y<0 (~ i)) ineq
        where
        ineq : x - y β₯ - (x + y)
        ineq = subst (x - y β₯_) (helper5 _ _) (+-rPresβ€ (β€-trans (inl (-Reverse>0 x>0)) (inl x>0)))
      case-split (lt y<0) (eq x+yβ‘0) =
        subst (abs x + abs y β₯_) (sym (xβ‘0βabsβ‘0 x+yβ‘0)) (+-Presβ₯0 absβ₯0 absβ₯0)
      case-split (lt y<0) (gt x+y>0) =
        transport (Ξ» i β x>0βabsβ‘x x>0 (~ i) + x<0βabsβ‘-x y<0 (~ i) β₯ x>0βabsβ‘x x+y>0 (~ i)) ineq
        where
        ineq : x - y β₯ x + y
        ineq = +-lPresβ€ (β€-trans (inl y<0) (inl (-Reverse<0 y<0)))


  absIneq+ : abs x + abs y β₯ abs (x + y)
  absIneq+ {x = x} {y = y} = case-split (<β€-total x 0r) (<β€-total y 0r)
    where
    case-split : _ β _ β _
    case-split (inr xβ₯0) _ = absIneq+Pos xβ₯0
    case-split _ (inr yβ₯0) = transport (Ξ» i β +Comm (abs y) (abs x) i β₯ abs (+Comm y x i)) (absIneq+Pos yβ₯0)
    case-split (inl x<0) (inl y<0) =
      inr (x<0βabsβ‘-x ineq β sym (helper5 _ _) β (Ξ» i β x<0βabsβ‘-x x<0 (~ i) + x<0βabsβ‘-x y<0 (~ i)))
      where
      ineq : x + y < 0r
      ineq = +-Pres<0 x<0 y<0

  Ξ-Inequality : abs (x - y) + abs (y - z) β₯ abs (x - z)
  Ξ-Inequality {x = x} {y = y} {z = z} =
    subst (Ξ» t β abs (x - y) + abs (y - z) β₯ abs t) (helper6 _ _ _) absIneq+


  {-

    Infinitesimal Closedness

  -}

  infinitesimalDiff : ((Ξ΅ : R) β (Ξ΅ > 0r) β abs (x - y) < Ξ΅) β x β‘ y
  infinitesimalDiff βΞ΅>β£x-yβ£ = diffβ‘0βxβ‘y (absβ‘0βxβ‘0 (infinitesimal absβ₯0 βΞ΅>β£x-yβ£))
