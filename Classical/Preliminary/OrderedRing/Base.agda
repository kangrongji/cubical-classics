{-

Totally Ordered Commutative Ring

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.OrderedRing.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

private
  variable
    ℓ ℓ' : Level


module _ (𝓡 : CommRing ℓ) where

  open RingTheory  (CommRing→Ring 𝓡)
  open CommRingStr (𝓡 .snd)

  private
    R = 𝓡 .fst
    isSetR = is-set


  module _ (_>0 : R → Type ℓ') where

    data Trichotomy>0 (x : R) : Type (ℓ-max ℓ ℓ') where
      lt : (- x) >0 → Trichotomy>0 x
      eq : x ≡ 0r   → Trichotomy>0 x
      gt : x >0     → Trichotomy>0 x


    module _
      (isProp< : (x : R) → isProp (x >0))
      (>0-asym : (x : R) → x >0 → (- x) >0 → ⊥)
      where

      >0-arefl : (x : R) → x >0 → x ≡ 0r → ⊥
      >0-arefl x x>0 x≡0 = >0-asym x x>0 -x>0
        where -x>0 : (- x) >0
              -x>0 = subst (_>0) (x≡0 ∙ sym 0Selfinverse ∙ (λ i → - (x≡0 (~ i)))) x>0

      isPropTrichotomy>0 : (x : R) → isProp (Trichotomy>0 x)
      isPropTrichotomy>0 x (lt -x>0) (lt -x>0') i = lt (isProp< (- x) -x>0 -x>0' i)
      isPropTrichotomy>0 x (eq  x≡0) (eq x≡0') i = eq (isSetR _ _ x≡0 x≡0' i)
      isPropTrichotomy>0 x (gt  x>0) (gt x>0') i = gt (isProp< x x>0 x>0' i)
      isPropTrichotomy>0 x (lt -x>0) (eq  x≡0) = Empty.rec (>0-arefl (- x) -x>0 -x≡0)
        where -x≡0 : - x ≡ 0r
              -x≡0 = (λ i → - (x≡0 i)) ∙ 0Selfinverse
      isPropTrichotomy>0 x (lt -x>0) (gt  x>0) = Empty.rec (>0-asym x x>0 -x>0)
      isPropTrichotomy>0 x (gt  x>0) (eq  x≡0) = Empty.rec (>0-arefl x x>0 x≡0)
      isPropTrichotomy>0 x (gt  x>0) (lt -x>0) = Empty.rec (>0-asym x x>0 -x>0)
      isPropTrichotomy>0 x (eq  x≡0) (lt -x>0) = Empty.rec (>0-arefl (- x) -x>0 -x≡0)
        where -x≡0 : - x ≡ 0r
              -x≡0 = (λ i → - (x≡0 i)) ∙ 0Selfinverse
      isPropTrichotomy>0 x (eq  x≡0) (gt  x>0) = Empty.rec (>0-arefl x x>0 x≡0)


  record OrderStrOnCommRing {ℓ' : Level} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

    constructor orderstr

    field

      _>0 : R → Type ℓ'
      isProp>0 : (x : R) → isProp (x >0)
      >0-asym : (x : R) → x >0 → (- x) >0 → ⊥
      >0-+ : (x y : R) → x >0 → y >0 → (x + y) >0
      >0-· : (x y : R) → x >0 → y >0 → (x · y) >0
      trichotomy>0 : (x : R) → Trichotomy>0 _>0 x


OrderedRing : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedRing ℓ ℓ' = Σ[ 𝓡 ∈ CommRing ℓ ] OrderStrOnCommRing 𝓡 {ℓ' = ℓ'}
