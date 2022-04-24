{-

Facts about Rational Numbers

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Preliminary.Rational where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty
open import Cubical.Data.Nat
  renaming (_·_ to _·ℕ_)
open import Cubical.Data.Nat.Order using ()
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int
  renaming (_·_ to _·ℤ_)
open import Cubical.HITs.Rationals.QuoQ

open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.HITs.SetQuotients as SetQuot
  using ([_]; eq/; discreteSetQuotients)

open import Cubical.Relation.Nullary hiding (∣_∣)

private
  variable
    p q r : ℚ

--open import Classical.Preliminary.Int
  --renaming (_<_ to _<ℤ_)


_<_ : ℚ → ℚ → Type
_<_ = {!!}

_≤_ : ℚ → ℚ → Type
_≤_ = {!!}

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


isFieldℚ : ¬ q ≡ 0 → Σ[ p ∈ ℚ ] (p · q ≡ 1) × (q · p ≡ 1)
isFieldℚ = {!!}

inv : ¬ q ≡ 0 → ℚ
inv q≢0 = isFieldℚ q≢0 .fst

∣_∣ : ℚ → ℚ
∣ q ∣ = {!!}



{-
_<0 : ℚ → Type
[ a , b ] <0 = (a ·ℤ ℕ₊₁→ℤ b) <ℤ 0
-}



{-
_<_ : ℚ → ℚ → Type
[ a / b ] < [ c / d ] = ℕ₊₁→ℤ b · ℕ₊₁→ℤ d · -}

