{-

Facts about Rational Numbers

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Preliminary.QuoQ where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.NatPlusOne
open import Cubical.HITs.SetQuotients as SetQuot hiding (_/_)
open import Cubical.Data.Int.MoreInts.QuoInt
  using    (ℤ ; pos ; neg)
  renaming (_·_ to _·ℤ_)
open import Cubical.HITs.Rationals.QuoQ
  renaming ([_/_] to [[_/_]])
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Relation.Nullary

open import Classical.Preliminary.QuoInt using (ℤOrder ; ℕ₊₁→ℤ>0 ; -1·n≡-n)
open import Classical.Preliminary.CommRing.Instances.QuoQ using ()
  renaming (ℚ to ℚRing)
open import Classical.Preliminary.QuoQ.Order using (ℚOrder)
open import Classical.Preliminary.OrderedRing

private
  variable
    p q r s : ℚ


{-

  Inclusion from Natural Numbers

-}

ℕ→ℚPos : ℕ → ℚ
ℕ→ℚPos n = [[ pos n / 1 ]]

ℕ→ℚNeg : ℕ → ℚ
ℕ→ℚNeg n = [[ neg n / 1 ]]


{-

  ℚ is a Field

-}

-- ℚ is a field

isFieldℚ : ¬ q ≡ 0 → Σ[ p ∈ ℚ ] (p · q ≡ 1) × (q · p ≡ 1)
isFieldℚ = {!!}

inv : ¬ q ≡ 0 → ℚ
inv q≢0 = isFieldℚ q≢0 .fst

·-lInv : (q≢0 : ¬ q ≡ 0) → inv q≢0 · q ≡ 1
·-lInv q≢0 = isFieldℚ q≢0 .snd .fst

·-rInv : (q≢0 : ¬ q ≡ 0) → q · inv q≢0 ≡ 1
·-rInv q≢0 = isFieldℚ q≢0 .snd .snd


{-

  The Ordering of ℚ

-}

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
