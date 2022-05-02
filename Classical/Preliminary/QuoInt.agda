{-

Facts about Integers

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.QuoInt where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x y : 𝓡 .fst) → (- x) · y ≡ - (x · y)
    helper1 = solve 𝓡


open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
  using    (ℕ ; zero ; suc)
  renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order using ()
  renaming (_<_ to _<ℕ_ ; _>_ to _>ℕ_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.MoreInts.QuoInt
  hiding   (_+_ ; _·_ ; -_)
open import Cubical.HITs.Rationals.QuoQ.Base using (ℕ₊₁→ℤ)

open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum

open import Classical.Preliminary.CommRing.Instances.QuoInt
  renaming (ℤ to ℤRing)
open import Classical.Algebra.OrderedRing

private
  variable
    x y z : ℤ
    m n k : ℤ


open Helpers ℤRing

open CommRingStr (ℤRing .snd)


-- Strictly larger thay zero

_>0 : ℤ → Type
(neg _) >0 = ⊥
(posneg i) >0 = ⊥
(pos zero) >0 = ⊥
(pos (suc y)) >0 = Unit

isProp>0 : (y : ℤ) → isProp (y >0)
isProp>0 (pos (suc y)) = isPropUnit

>0-asym : (y : ℤ) → y >0 → (- y) >0 → ⊥
>0-asym (pos (suc y)) _ p = p

>0-+ : (x y : ℤ) → x >0 → y >0 → (x + y) >0
>0-+ (pos (suc x)) (pos (suc y)) _ _ =
  subst (_>0) (signed-distrib spos (suc x) (suc y)) _

>0-· : (x y : ℤ) → x >0 → y >0 → (x · y) >0
>0-· (pos (suc x)) (pos (suc y)) _ _ =
  subst (_>0) (sym (·-signed-pos {s = spos} (suc x) (suc y))) _

trichotomy>0 : (x : ℤ) → Trichotomy>0 ℤRing _>0 x
trichotomy>0 (neg (suc _)) = lt _
trichotomy>0 (signed spos zero) = eq refl
trichotomy>0 (signed sneg zero) = eq (sym posneg)
trichotomy>0 (posneg i) = eq (λ j → posneg (i ∧ ~ j))
trichotomy>0 (pos (suc _)) = gt _


{-

  ℤ as ordered ring

-}

ℤOrder : OrderedRing _ _
ℤOrder = ℤRing , orderstr _>0 isProp>0 >0-asym >0-+ >0-· trichotomy>0

open OrderedRingStr ℤOrder

ℕ₊₁→ℤ>0 : (n : ℕ₊₁) → ℕ₊₁→ℤ n > 0
ℕ₊₁→ℤ>0 n = transport (>0≡>0r (ℕ₊₁→ℤ n)) (helper n)
  where helper : (n : ℕ₊₁) → ℕ₊₁→ℤ n >0
        helper (1+ n) = _

-1·n≡-n : (n : ℤ) → -1 · n ≡ - n
-1·n≡-n n = helper1 1 n ∙ (λ i → - (·Lid n i))
