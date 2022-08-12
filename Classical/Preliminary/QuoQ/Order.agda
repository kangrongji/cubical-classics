{-

Ordering of Rational Numbers

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.QuoQ.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : 1r · 1r + (- 0r) · 1r ≡ 1r
    helper1 = solve 𝓡


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.MoreInts.QuoInt
  using    (ℤ ; pos ; neg)
  renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.HITs.Rationals.QuoQ
open import Cubical.HITs.SetQuotients as SetQuot
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.QuoQ
  using    (ℚCommRing)
open import Cubical.Relation.Nullary

open import Classical.Algebra.OrderedRing.Instances.QuoInt
  using    (ℤOrderedRing ; ℕ₊₁→ℤ>0 ; -1·n≡-n)
open import Classical.Algebra.OrderedRing

private
  variable
    p q r s : ℚ


open OrderedRingStr ℤOrderedRing
open RingTheory  (CommRing→Ring (ℤOrderedRing .fst))

private
  >0-path : (x y : ℤ × ℕ₊₁)(r : x ∼ y) → (x .fst > 0) ≡ (y .fst > 0)
  >0-path (a , b) (c , d) r = hPropExt (isProp< {0} {a}) (isProp< {0} {c}) a>0→c>0 c>0→a>0
    where
    a>0→c>0 : a > 0 → c > 0
    a>0→c>0 a>0 =
      let a·d>0 : a ·ℤ (ℕ₊₁→ℤ d) > 0
          a·d>0 = ·-Pres>0 {x = a} {y = ℕ₊₁→ℤ d} a>0 (ℕ₊₁→ℤ>0 d)
          c·b>0 : c ·ℤ (ℕ₊₁→ℤ b) > 0
          c·b>0 = subst (_> 0) r a·d>0
      in  ·-lPosCancel>0 {x = ℕ₊₁→ℤ b} {y = c} (ℕ₊₁→ℤ>0 b) c·b>0
    c>0→a>0 : c > 0 → a > 0
    c>0→a>0 c>0 =
      let c·b>0 : c ·ℤ (ℕ₊₁→ℤ b) > 0
          c·b>0 = ·-Pres>0 {x = c} {y = ℕ₊₁→ℤ b} c>0 (ℕ₊₁→ℤ>0 b)
          a·d>0 : a ·ℤ (ℕ₊₁→ℤ d) > 0
          a·d>0 = subst (_> 0) (sym r) c·b>0
      in  ·-lPosCancel>0 {x = ℕ₊₁→ℤ d} {y = a} (ℕ₊₁→ℤ>0 d) a·d>0

  >0-prop : ℤ × ℕ₊₁ → hProp ℓ-zero
  >0-prop (a , _) = (a > 0) , isProp< {0} {a}

  >0-prop-path : (x y : ℤ × ℕ₊₁)(r : x ∼ y) → >0-prop x ≡ >0-prop y
  >0-prop-path x y r i .fst = >0-path x y r i
  >0-prop-path x y r i .snd = isProp→PathP (λ i → isPropIsProp {A = >0-path x y r i}) (>0-prop x .snd) (>0-prop y .snd) i

_>0-Prop : ℚ → hProp ℓ-zero
_>0-Prop = SetQuot.elim (λ _ → isOfHLevelTypeOfHLevel 1) >0-prop >0-prop-path

_>0 : ℚ → Type
q >0 = (q >0-Prop) .fst

isProp>0 : (q : ℚ) → isProp (q >0)
isProp>0 q = (q >0-Prop) .snd

private
  >0-asym-helper : (x : ℤ × ℕ₊₁) → [ x ] >0 → (- [ x ]) >0 → ⊥
  >0-asym-helper (a , _) a>0 -1·a>0 = <-asym {x = 0} {y = a} a>0 (-Reverse->0 {x = a} -a>0)
    where -a>0 : -ℤ a > 0
          -a>0 = subst (_> 0) (-1·n≡-n a) -1·a>0

>0-asym : (q : ℚ) → q >0 → (- q) >0 → ⊥
>0-asym = elimProp (λ _ → isPropΠ2 (λ _ _ → isProp⊥)) >0-asym-helper

>0-+ : (p q : ℚ) → p >0 → q >0 → (p + q) >0
>0-+ = elimProp2 (λ p q → isPropΠ2 (λ _ _ → isProp>0 (p + q)))
  (λ (a , b) (c , d) a>0 c>0 →
    let a·d>0 : a ·ℤ (ℕ₊₁→ℤ d) > 0
        a·d>0 = ·-Pres>0 {x = a} {y = ℕ₊₁→ℤ d} a>0 (ℕ₊₁→ℤ>0 d)
        c·b>0 : c ·ℤ (ℕ₊₁→ℤ b) > 0
        c·b>0 = ·-Pres>0 {x = c} {y = ℕ₊₁→ℤ b} c>0 (ℕ₊₁→ℤ>0 b)
    in  +-Pres>0 {x = a ·ℤ (ℕ₊₁→ℤ d)} {y = c ·ℤ (ℕ₊₁→ℤ b)} a·d>0 c·b>0)

>0-· : (p q : ℚ) → p >0 → q >0 → (p · q) >0
>0-· = elimProp2 (λ p q → isPropΠ2 (λ _ _ → isProp>0 (p · q)))
  (λ (a , _) (c , _) a>0 c>0 → ·-Pres>0 {x = a} {y = c} a>0 c>0)

private
  trichotomy>0-helper : (x : ℤ × ℕ₊₁) → Trichotomy>0 ℚCommRing _>0 [ x ]
  trichotomy>0-helper (a , b) with trichotomy a 0
  ... | lt a<0 = lt (subst (_> 0) (sym (-1·n≡-n a)) (-Reverse<0 {x = a} a<0))
  ... | eq a≡0 = eq (eq/ (a , b) (0 , 1) (a·1≡0 ∙ sym 0·b≡0))
    where a·1≡0 : a ·ℤ 1 ≡ 0
          a·1≡0 = (λ i → a≡0 i ·ℤ 1) ∙ 0LeftAnnihilates 1
          0·b≡0 : 0 ·ℤ ℕ₊₁→ℤ b ≡ 0
          0·b≡0 = 0LeftAnnihilates (ℕ₊₁→ℤ b)
  ... | gt a>0 = gt a>0

trichotomy>0 : (q : ℚ) → Trichotomy>0 ℚCommRing _>0 q
trichotomy>0 = elimProp (isPropTrichotomy>0 ℚCommRing _>0 isProp>0 >0-asym) trichotomy>0-helper


{-

  ℚ is a totally ordered ring

-}

ℚOrderedRing : OrderedRing _ _
ℚOrderedRing = ℚCommRing , orderstr _>0 isProp>0 1>0' >0-asym >0-+ >0-· trichotomy>0
  where
  open Helpers (ℤOrderedRing .fst)
  1>0' : 1 > 0
  1>0' = subst (_> 0) helper1 _
