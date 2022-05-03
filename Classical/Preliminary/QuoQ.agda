{-

Facts about Rational Numbers

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.QuoQ where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (p q : 𝓡 .fst) → ((p + q) + (1r + 1r) · (- p)) ≡ q - p
    helper1 = solve 𝓡


open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.NatPlusOne
open import Cubical.HITs.Rationals.QuoQ using (ℚ)
open import Cubical.Algebra.Ring
open import Cubical.Relation.Nullary

open import Classical.Preliminary.QuoInt using (ℤOrder)
open import Classical.Preliminary.QuoQ.Base public
open import Classical.Preliminary.QuoQ.Field using (ℚField ; _/_ ; ·-/-lInv) public
open import Classical.Preliminary.QuoQ.Order using (ℚOrder ; 1>0) public
open import Classical.Algebra.Field
open import Classical.Algebra.OrderedRing

private
  variable
    p q r s : ℚ


{-

  The Ordering of ℚ

-}

open FieldStr       ℚField
open OrderedRingStr ℚOrder

open Helpers (ℚOrder .fst)


2>0 : 2 > 0
2>0 = +-Pres>0 {x = 1} {y = 1} 1>0 1>0

-1<0 : - 1 < 0
-1<0 = -Reverse>0 {x = 1} 1>0

q+1>q : q + 1 > q
q+1>q {q = q} = +-rPos→> {x = 1} {y = q} 1>0

q-1<q : q - 1 < q
q-1<q {q = q} = +-rNeg→< {x = - 1} {y = q} -1<0


middle : (p q : ℚ) → ℚ
middle p q = (p + q) / 2

middle-sym : (p q : ℚ) → middle p q ≡ middle q p
middle-sym p q i = (+Comm p q i) / 2

2·middle : (p q : ℚ) → 2 · middle p q ≡ p + q
2·middle p q = ·-/-lInv (p + q) 2

middle-l : (p q : ℚ) → 2 · (middle p q - p) ≡ q - p
middle-l p q = ·Rdist+ 2 (middle p q) _ ∙ (λ i → 2·middle p q i + 2 · (- p)) ∙ helper1 p q

middle-r : (p q : ℚ) → 2 · (middle p q - q) ≡ p - q
middle-r p q = (λ i → 2 · (middle-sym p q i - q)) ∙ middle-l q p

middle>l : p < q → middle p q > p
middle>l {p = p} {q = q} p<q =
  Diff>0→> {x = middle p q} {y = p} (·-rPosCancel>0 {x = 2} {y = middle p q - p} 2>0
    (subst (_> 0) (sym (middle-l p q)) (>→Diff>0 {x = q} {y = p} p<q)))

middle<r : p < q → q > middle p q
middle<r {p = p} {q = q} p<q =
  Diff<0→< {x = middle p q} {y = q} (·-rPosCancel<0 {x = 2} {y = middle p q - q} 2>0
    (subst (_< 0) (sym (middle-r p q)) (<→Diff<0 {x = p} {y = q} p<q)))


p>0→p⁻¹>0 : (p>0 : p > 0) → inv (>-arefl {x = p} p>0) > 0
p>0→p⁻¹>0 {p = p} p>0 = ·-rPosCancel>0 {x = p} {y = inv (>-arefl {x = p} p>0)} p>0 p·p⁻¹>0
  where p·p⁻¹>0 : p · inv (>-arefl {x = p} p>0) > 0
        p·p⁻¹>0 = subst (_> 0) (sym (·-rInv (>-arefl {x = p} p>0))) 1>0

p>q>0→p·q⁻¹>1 : (q>0 : q > 0) → p > q → p · inv (>-arefl {x = q} q>0) > 1
p>q>0→p·q⁻¹>1 {q = q} {p = p} q>0 p>q =
  subst (p · inv (>-arefl {x = q} q>0) >_) (·-rInv (>-arefl {x = q} q>0))
    (·-rPosPres< {x = inv (>-arefl {x = q} q>0)} {y = q} {z = p} (p>0→p⁻¹>0 {p = q} q>0) p>q)
