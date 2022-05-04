{-

Totally Ordered Commutative Ring

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.HalfOrderedRing.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup

private
  variable
    ℓ ℓ' : Level


module _ (𝒜 : AbGroup ℓ) where

  open AbGroupStr (𝒜 .snd)

  private
    A = 𝒜 .fst
    isSetA = is-set


  module _ (_>0 : A → Type ℓ') where

    data Trichotomy>0 (x : A) : Type (ℓ-max ℓ ℓ') where
      lt : (- x) >0 → Trichotomy>0 x
      eq : x ≡ 0g   → Trichotomy>0 x
      gt : x >0     → Trichotomy>0 x


  record OrderedAbGroup {ℓ' : Level} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

    constructor halforderstr

    field

      _>0 : A → Type ℓ'
      isProp>0 : (x : A) → isProp (x >0)
      >0-asym : (x : A) → x >0 → (- x) >0 → ⊥
      >0-+ : (x y : A) → x >0 → y >0 → (x + y) >0
      trichotomy>0 : (x : A) → Trichotomy>0 _>0 x

      _·_ : A → A → A
      ·Comm : (x y : A) → x · y ≡ y · x
      >0-· : (x y : A) → x >0 → y >0 → (x · y) >0


record IsRing {R : Type ℓ}
              (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where

  constructor isring

  field
    +IsAbGroup : IsAbGroup 0r _+_ -_
    ·IsMonoid  : IsMonoid 1r _·_
    dist        : (x y z : R) → (x · (y + z) ≡ (x · y) + (x · z))
                              × ((x + y) · z ≡ (x · z) + (y · z))

{-
OrderedRing : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedRing ℓ ℓ' = Σ[ 𝓡 ∈ CommRing ℓ ] OrderStrOnCommRing 𝓡 {ℓ' = ℓ'}
-}