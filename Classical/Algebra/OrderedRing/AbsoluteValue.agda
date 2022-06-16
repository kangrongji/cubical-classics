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
    ℓ ℓ' : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x : 𝓡 .fst) → x ≡ (x - 0r)
    helper1 = solve 𝓡

    helper2 : (x y d : 𝓡 .fst) → ((x - d) + d) - y ≡ x - y
    helper2 = solve 𝓡

    helper3 : (x y d : 𝓡 .fst) → (y + d) - y ≡ d
    helper3 = solve 𝓡

    helper4 : (x y d : 𝓡 .fst) → (y + d) - y ≡ d
    helper4 = solve 𝓡

    helper5 : (x y : 𝓡 .fst) → - x - y ≡ - (x + y)
    helper5 = solve 𝓡

    helper6 : (x y z : 𝓡 .fst) → (x - y) + (y - z) ≡ x - z
    helper6 = solve 𝓡

    helper7 : (x d : 𝓡 .fst) → x ≡ (x + d) - d
    helper7 = solve 𝓡

    helper8 : (x y : 𝓡 .fst) → y - x ≡ - (x - y)
    helper8 = solve 𝓡

    helper9 : (x d : 𝓡 .fst) → (x + d) - x ≡ d
    helper9 = solve 𝓡


module AbsoluteValue (𝓡 : OrderedRing ℓ ℓ') where

  private
    R = 𝓡 .fst .fst

  open RingTheory (CommRing→Ring (𝓡 .fst))
  open CommRingStr   (𝓡 .fst .snd)
  open OrderedRingStr 𝓡

  open Helpers (𝓡 .fst)


  private
    variable
      x y z d : R


  abs : R → R
  abs x with trichotomy x 0r
  ... | lt x<0 = - x
  ... | eq x≡0 = 0r
  ... | gt x>0 = x

  abs≥0 : abs x ≥ 0r
  abs≥0 {x = x} with trichotomy x 0r
  ... | lt x<0 = inl (-Reverse<0 x<0)
  ... | eq x≡0 = inr refl
  ... | gt x>0 = inl x>0

  abs≡0→x≡0 : abs x ≡ 0r → x ≡ 0r
  abs≡0→x≡0 {x = x} abs≡0 with trichotomy x 0r
  ... | lt x<0 = sym (-Idempotent _) ∙ (λ i → - abs≡0 i) ∙ 0Selfinverse
  ... | eq x≡0 = x≡0
  ... | gt x>0 = abs≡0


  x>0→abs≡x : x > 0r → abs x ≡ x
  x>0→abs≡x {x = x} x>0 with trichotomy x 0r
  ... | lt x<0 = Empty.rec (<-asym  x>0 x<0)
  ... | eq x≡0 = Empty.rec (<-arefl x>0 (sym x≡0))
  ... | gt x>0 = refl

  x<0→abs≡-x : x < 0r → abs x ≡ - x
  x<0→abs≡-x {x = x} x<0 with trichotomy x 0r
  ... | lt x<0 = refl
  ... | eq x≡0 = Empty.rec (<-arefl x<0 x≡0)
  ... | gt x>0 = Empty.rec (<-asym  x>0 x<0)

  x≡0→abs≡0 : x ≡ 0r → abs x ≡ 0r
  x≡0→abs≡0 {x = x} x≡0 with trichotomy x 0r
  ... | lt x<0 = Empty.rec (<-arefl x<0 x≡0)
  ... | eq x≡0 = refl
  ... | gt x>0 = Empty.rec (<-arefl x>0 (sym x≡0))


  x≥0→abs≡x : x ≥ 0r → abs x ≡ x
  x≥0→abs≡x {x = x} x≥0 with trichotomy x 0r
  ... | lt x<0 = Empty.rec (<≤-asym x<0 x≥0)
  ... | eq x≡0 = sym x≡0
  ... | gt x>0 = refl

  x≤0→abs≡-x : x ≤ 0r → abs x ≡ - x
  x≤0→abs≡-x {x = x} x≤0 with trichotomy x 0r
  ... | lt x<0 = refl
  ... | eq x≡0 = sym 0Selfinverse ∙ (λ i → - x≡0 (~ i))
  ... | gt x>0 = Empty.rec (<≤-asym x>0 x≤0)


  absx≡→abs-x : abs x ≡ abs (- x)
  absx≡→abs-x {x = x} with trichotomy x 0r
  ... | lt x<0 = sym (x>0→abs≡x (-Reverse<0 x<0))
  ... | eq x≡0 = sym (x≡0→abs≡0 refl) ∙ (λ i → abs (0Selfinverse (~ i))) ∙ (λ i → abs (- x≡0 (~ i)))
  ... | gt x>0 = sym (-Idempotent _) ∙ sym (x<0→abs≡-x (-Reverse>0 x>0))


  absSuppress≤ : x ≤ z → abs (x - y) < d → y < z + d
  absSuppress≤ {x = x} {y = y} {d = d} x≤z ∣x-y∣<d = case-split (<≤-total y x)
    where
    case-split : (x > y) ⊎ (x ≤ y) → _
    case-split (inl x>y) = <-trans (<≤-trans x>y x≤z) (+-rPos→> (≤<-trans abs≥0 ∣x-y∣<d))
    case-split (inr x≤y) = <≤-trans (-MoveLToR<' y-x<d) (+-rPres≤ x≤z)
      where
      y-x<d : y - x < d
      y-x<d = subst (_< d) (x≤0→abs≡-x (≤→Diff≤0 x≤y) ∙ (sym (helper8 _ _))) ∣x-y∣<d

  absSuppress≥ : z ≤ x → abs (x - y) < d → z - d < y
  absSuppress≥ {x = x} {y = y} {d = d} z≤x ∣x-y∣<d = case-split (<≤-total x y)
    where
    case-split : (y > x) ⊎ (y ≤ x) → _
    case-split (inl y>x) = <-trans (-rPos→< (≤<-trans abs≥0 ∣x-y∣<d)) (≤<-trans z≤x y>x)
    case-split (inr y≤x) = ≤<-trans (+-rPres≤ z≤x) (+-MoveRToL< (-MoveLToR<' x-y<d))
      where
      x-y<d : x - y < d
      x-y<d = subst (_< d) (x≥0→abs≡x (≥→Diff≥0 y≤x)) ∣x-y∣<d


  absKeepSign+ : x > 0r → abs (x - y) < x → y > 0r
  absKeepSign+ {x = x} {y = y} x>0 ∣x-y∣<x with trichotomy y 0r
  ... | lt y<0 = Empty.rec (<-asym ∣x-y∣<x (subst (_> x) (sym ∣x-y∣≡x-y) x-y>x))
    where
    x-y>x : x - y > x
    x-y>x = +-rPos→> (-Reverse<0 y<0)
    ∣x-y∣≡x-y : abs (x - y) ≡ x - y
    ∣x-y∣≡x-y =  x>0→abs≡x (<-trans x>0 x-y>x)
  ... | eq y≡0 = Empty.rec (<-arefl (subst (_< x) ∣x-y∣≡x ∣x-y∣<x) refl)
    where
    ∣x-y∣≡x : abs (x - y) ≡ x
    ∣x-y∣≡x = (λ i → abs (x - y≡0 i)) ∙ (λ i → abs (helper1 x (~ i))) ∙ x>0→abs≡x x>0
  ... | gt y>0 = y>0

  absKeepSign- : x < 0r → abs (x - y) < - x → y < 0r
  absKeepSign- {x = x} {y = y} x<0 ∣x-y∣<-x with trichotomy y 0r
  ... | lt y<0 = y<0
  ... | eq y≡0 = Empty.rec (<-arefl (subst (_< - x) ∣x-y∣≡x ∣x-y∣<-x) refl)
    where
    ∣x-y∣≡x : abs (x - y) ≡ - x
    ∣x-y∣≡x = (λ i → abs (x - y≡0 i)) ∙ (λ i → abs (helper1 x (~ i))) ∙ x<0→abs≡-x x<0
  ... | gt y>0 = Empty.rec (<-asym ∣x-y∣<-x (subst (_> - x) (sym ∣x-y∣≡-x-y) (-Reverse< x-y<x)))
    where
    x-y<x : x - y < x
    x-y<x = -rPos→< y>0
    ∣x-y∣≡-x-y : abs (x - y) ≡ - (x - y)
    ∣x-y∣≡-x-y =  x<0→abs≡-x (<-trans x-y<x x<0)


  absInBetween : d > 0r → x - d ≤ y → y ≤ x → abs (x - y) ≤ d
  absInBetween {d = d} {x = x} {y = y} d>0 x-d≤y y≤x = subst (_≤ d) x-y≡∣x-y∣ x-y≤d
    where
    x-y≤d : x - y ≤ d
    x-y≤d = transport (λ i → helper2 x y d i ≤ helper3 x y d i) (+-rPres≤ (+-rPres≤ x-d≤y))
    x-y≡∣x-y∣ : x - y ≡ abs (x - y)
    x-y≡∣x-y∣ = sym (x≥0→abs≡x (≥→Diff≥0 y≤x))

  absInBetween< : d > 0r → x - d < y → y < x → abs (x - y) < d
  absInBetween< {d = d} {x = x} {y = y} d>0 x-d<y y<x = subst (_< d) x-y≡∣x-y∣ x-y<d
    where
    x-y<d : x - y < d
    x-y<d = transport (λ i → helper2 x y d i < helper3 x y d i) (+-rPres< (+-rPres< x-d<y))
    x-y≡∣x-y∣ : x - y ≡ abs (x - y)
    x-y≡∣x-y∣ = sym (x>0→abs≡x (>→Diff>0 y<x))

  absInBetween<' : d > 0r → x < y → y < x + d → abs (x - y) < d
  absInBetween<' {d = d} {x = x} {y = y} d>0 x<y y<x+d = subst (_< d) x-y≡∣x-y∣ x-y<d
    where
    x-y<d : y - x < d
    x-y<d = transport (λ i → y - x < helper9 x d i) (+-rPres< y<x+d)
    x-y≡∣x-y∣ : y - x ≡ abs (x - y)
    x-y≡∣x-y∣ = helper8 _ _ ∙ sym (x<0→abs≡-x (<→Diff<0 x<y))

  absInOpenInterval : d > 0r → x - d < y → y < x + d → abs (x - y) < d
  absInOpenInterval {d = d} {x = x} {y = y} d>0 x-d<y y<x+d = case-split (trichotomy x y)
    where
    case-split : Trichotomy x y → _
    case-split (gt x>y) = absInBetween<  d>0 x-d<y x>y
    case-split (lt x<y) = absInBetween<' d>0 x<y y<x+d
    case-split (eq x≡y) = subst (_< d) (sym (x≡0→abs≡0 (x≡y→diff≡0 x≡y))) d>0

  absInBetween<≤ : d > 0r → x - d < y → y ≤ x → abs (x - y) < d
  absInBetween<≤ d>0 x-d<y y≤x = absInOpenInterval d>0 x-d<y (≤<-trans y≤x (+-rPos→> d>0))


  private
    absIneq+Pos : x ≥ 0r → abs x + abs y ≥ abs (x + y)
    absIneq+Pos {x = x} {y = y} (inr 0≡x) =
      transport (λ i → left (~ i) ≥ right (~ i)) (inr refl)
      where
      left : abs x + abs y ≡ abs y
      left = (λ i → x≡0→abs≡0 (sym 0≡x) i + abs y) ∙ +IdL _
      right : abs (x + y) ≡ abs y
      right = cong abs ((λ i → 0≡x (~ i) + y) ∙ +IdL _)
    absIneq+Pos {x = x} {y = y} (inl x>0) = case-split (trichotomy y 0r) (trichotomy (x + y) 0r)
      where
      case-split : Trichotomy y 0r → Trichotomy (x + y) 0r → _
      case-split (eq y≡0) _ =
        transport (λ i → left (~ i) ≥ right (~ i)) (inr refl)
        where
        left : abs x + abs y ≡ abs x
        left = (λ i → abs x + x≡0→abs≡0 y≡0 i) ∙ +IdR _
        right : abs (x + y) ≡ abs x
        right = cong abs ((λ i → x + y≡0 i) ∙ +IdR _)
      case-split (gt y>0) _ =
        transport (λ i → x>0→abs≡x x>0 (~ i) + x>0→abs≡x y>0 (~ i) ≥ x>0→abs≡x ineq (~ i)) (inr refl)
        where
        ineq : x + y > 0r
        ineq = +-Pres>0 x>0 y>0
      case-split (lt y<0) (lt x+y<0) =
        transport (λ i → x>0→abs≡x x>0 (~ i) + x<0→abs≡-x y<0 (~ i) ≥ x<0→abs≡-x x+y<0 (~ i)) ineq
        where
        ineq : x - y ≥ - (x + y)
        ineq = subst (x - y ≥_) (helper5 _ _) (+-rPres≤ (≤-trans (inl (-Reverse>0 x>0)) (inl x>0)))
      case-split (lt y<0) (eq x+y≡0) =
        subst (abs x + abs y ≥_) (sym (x≡0→abs≡0 x+y≡0)) (+-Pres≥0 abs≥0 abs≥0)
      case-split (lt y<0) (gt x+y>0) =
        transport (λ i → x>0→abs≡x x>0 (~ i) + x<0→abs≡-x y<0 (~ i) ≥ x>0→abs≡x x+y>0 (~ i)) ineq
        where
        ineq : x - y ≥ x + y
        ineq = +-lPres≤ (≤-trans (inl y<0) (inl (-Reverse<0 y<0)))


  absIneq+ : abs x + abs y ≥ abs (x + y)
  absIneq+ {x = x} {y = y} = case-split (<≤-total x 0r) (<≤-total y 0r)
    where
    case-split : _ → _ → _
    case-split (inr x≥0) _ = absIneq+Pos x≥0
    case-split _ (inr y≥0) = transport (λ i → +Comm (abs y) (abs x) i ≥ abs (+Comm y x i)) (absIneq+Pos y≥0)
    case-split (inl x<0) (inl y<0) =
      inr (x<0→abs≡-x ineq ∙ sym (helper5 _ _) ∙ (λ i → x<0→abs≡-x x<0 (~ i) + x<0→abs≡-x y<0 (~ i)))
      where
      ineq : x + y < 0r
      ineq = +-Pres<0 x<0 y<0

  Δ-Inequality : abs (x - y) + abs (y - z) ≥ abs (x - z)
  Δ-Inequality {x = x} {y = y} {z = z} =
    subst (λ t → abs (x - y) + abs (y - z) ≥ abs t) (helper6 _ _ _) absIneq+


  {-

    Infinitesimal Closedness

  -}

  infinitesimalDiff : ((ε : R) → (ε > 0r) → abs (x - y) < ε) → x ≡ y
  infinitesimalDiff ∀ε>∣x-y∣ = diff≡0→x≡y (abs≡0→x≡0 (infinitesimal abs≥0 ∀ε>∣x-y∣))
