{-

Facts about Rational Numbers

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Preliminary.QuoQ where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x y : 𝓡 .fst) → (x · y) · 1r ≡ 1r · (y · x)
    helper1 = solve 𝓡

    helper2 : (x y : 𝓡 .fst) → ((- x) · (- y)) · 1r ≡ 1r · (y · x)
    helper2 = solve 𝓡


open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.NatPlusOne
open import Cubical.HITs.Rationals.QuoQ using (ℚ)
open import Cubical.Algebra.Ring
open import Cubical.Relation.Nullary

open import Classical.Preliminary.QuoQ.Base public
open import Classical.Preliminary.QuoQ.Field using (ℚField) public
open import Classical.Preliminary.QuoQ.Order using (ℚOrder) public
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

-- Compatibility

≤-+ : p ≤ q → p + r ≤ q + r
≤-+ = {!!}

mult-pres-≥0 : p ≥ 0 → q ≥ 0 → p · q ≥ 0
mult-pres-≥0 = {!!}

--------------


¬q<q : ¬ q < q
¬q<q {q = q} h = <-asym {x = q} {y = q} h h


q-1<q : q - 1 < q
q-1<q = {!!}

q+1>q : q + 1 > q
q+1>q = {!!}

_/_ : ℚ → ℕ₊₁ → ℚ
p / n = {!!}

middle : (p q : ℚ) → ℚ
middle p q = (p + q) / 2

middle>l : p < q → middle p q > p
middle>l = {!!}

middle<r : p < q → q > middle p q
middle<r = {!!}


+-<-+ : p < q → r < s → p + r < q + s
+-<-+ = {!!}

<-+ : p < q → r + p < r + q
<-+ = {!!}

<-+-pos : q > 0 → p + q > p
<-+-pos = {!!}

p>q→p-q>0 : p > q → p - q > 0
p>q→p-q>0 = {!!}

<-+-neg : q < 0 → p + q < p
<-+-neg = {!!}

p<q→p-q<0 : p < q → p - q < 0
p<q→p-q<0 = {!!}

>0-+-pos : p > 0 → q > 0 → p + q > 0
>0-+-pos = {!!}



-Involutive : - (- p) ≡ p
-Involutive = {!!}

-reverse< : p < q → - p > - q
-reverse< = {!!}

-reverse<' : - p < - q → p > q
-reverse<' = {!!}

-recog : p + q ≡ 0 → p ≡ - q
-recog = {!!}

q>0→q≢0 : q > 0 → ¬ q ≡ 0
q>0→q≢0 = {!!}

1q : ℚ
1q = 1

0q : ℚ
0q = 0

r>q>0→r/q>1 : (q>0 : q > 0) → r > q → r · inv (q>0→q≢0 {q = q} q>0) > 1q
r>q>0→r/q>1 = {!!}

p>0+q>1→pq>p : (p>0 : p > 0) → q > 1q → p · q > p
p>0+q>1→pq>p = {!!}

>0-·-pos : p > 0 → q > 0 → p · q > 0
>0-·-pos = {!!}

·-<-·-pos : p > 0 → r > 0 → p < q → r < s → p · r < q · s
·-<-·-pos = {!!}

·-<-·-pos-l : p > 0 → r > 0 → p < q → p · r < q · r
·-<-·-pos-l = {!!}


-1<0 : - 1q < 0
-1<0 = {!!}


<-·-q>1 : p > 0 → q > 1 → p · r > p
<-·-q>1 = {!!}

p>q>0→p·q⁻¹>1 : (q>0 : q > 0) → p > q → p · inv (q>0→q≢0 {q = q} q>0) > 1q
p>q>0→p·q⁻¹>1 = {!!}

p>0→p⁻¹>0 : (p>0 : p > 0) → inv (q>0→q≢0 {q = p} p>0) > 0q
p>0→p⁻¹>0 = {!!}
