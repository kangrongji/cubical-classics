{-

Facts about Rational Numbers

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Preliminary.Rational where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty
open import Cubical.Data.Nat
  renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order using ()
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.MoreInts.QuoInt
  using    (pos ; neg)
open import Cubical.HITs.Rationals.QuoQ
  renaming ([_/_] to [[_/_]])

open import Cubical.Data.Sum
open import Cubical.Data.Sigma


open import Cubical.Relation.Nullary hiding (∣_∣)

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

  ℚ is a Totally Ordered Field

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


-- ℚ has total order

infix 4 _≤_ _≥_

_≤_ : ℚ → ℚ → Type
_≤_ = {!!}

_≥_ : ℚ → ℚ → Type
p ≥ q = q ≤ p

≤-refl : q ≤ q
≤-refl = {!!}

≤-trans : p ≤ q → q ≤ r → p ≤ r
≤-trans = {!!}

≤-asym : p ≤ q → q ≤ p → p ≡ q
≤-asym = {!!}

≤-total : (p ≤ q) ⊎ (q ≤ p)
≤-total = {!!}

-- Compatibility

≤-+ : p ≤ q → p + r ≤ q + r
≤-+ = {!!}

mult-pres-≥0 : p ≥ 0 → q ≥ 0 → p · q ≥ 0
mult-pres-≥0 = {!!}








--------------

ℕ→ℚ : ℕ → ℚ
ℕ→ℚ n = {!!}


_<_ : ℚ → ℚ → Type
_<_ = {!!}


_>_ : ℚ → ℚ → Type
p > q = q < p

infix 4 _<_ _>_

isProp< : isProp (p < q)
isProp< = {!!}


data Trichotomy (p q : ℚ) : Type where
  lt : p < q → Trichotomy p q
  eq : p ≡ q → Trichotomy p q
  gt : p > q → Trichotomy p q

trichotomy< : (p q : ℚ) → Trichotomy p q
trichotomy< p q = {!!}

<-trans : p < q → q < r → p < r
<-trans = {!!}

<-asym : p < q → q < p → ⊥
<-asym = {!!}

¬q<q : ¬ q < q
¬q<q {q = q} h = <-asym {p = q} {q = q} h h




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
