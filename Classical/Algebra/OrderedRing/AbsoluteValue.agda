{-

Absolute Value

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedRing.AbsoluteValue where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as Empty

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
    x-y<x = +-rNeg→< (-Reverse>0 y>0)
    ∣x-y∣≡-x-y : abs (x - y) ≡ - (x - y)
    ∣x-y∣≡-x-y =  x<0→abs≡-x (<-trans x-y<x x<0)


  absInBetween : d > 0r → x - d ≤ y → y ≤ x → abs (x - y) ≤ d
  absInBetween {d = d} {x = x} {y = y} d>0 x-d≤y y≤x = subst (_≤ d) x-y≡∣x-y∣ x-y≤d
    where
    x-y≤d : x - y ≤ d
    x-y≤d = transport (λ i → helper2 x y d i ≤ helper3 x y d i) (+-rPres≤ (+-rPres≤ x-d≤y))
    x-y≡∣x-y∣ : x - y ≡ abs (x - y)
    x-y≡∣x-y∣ = sym (x≥0→abs≡x (≥→Diff≥0 y≤x))
