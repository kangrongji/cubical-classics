{-

Facts about Integers

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedRing.Instances.QuoInt where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
private
  module Helpers {β : Level}(π‘ : CommRing β) where
    open CommRingStr (π‘ .snd)

    helper1 : (x y : π‘ .fst) β (- x) Β· y β‘ - (x Β· y)
    helper1 = solve π‘

    helper2 : (a b : π‘ .fst) β a - b β‘ (a - 1r) + 1r - b
    helper2 = solve π‘

    helper3 : (b : π‘ .fst) β b + 1r - b β‘ 1r
    helper3 = solve π‘


open import Cubical.Data.Nat
  using    (β ; zero ; suc)
  renaming (_+_ to _+β_ ; _Β·_ to _Β·β_)
open import Cubical.Data.Nat.Order using ()
  renaming (_<_ to _<β_ ; _>_ to _>β_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.MoreInts.QuoInt
  hiding   (_+_ ; _Β·_ ; -_)
open import Cubical.HITs.Rationals.QuoQ.Base using (βββββ€)
open import Cubical.Algebra.CommRing.Instances.QuoInt

open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum

open import Classical.Algebra.OrderedRing

private
  variable
    x y z : β€
    m n k : β€


open Helpers β€CommRing
open CommRingStr (β€CommRing .snd)


-- Strictly larger thay zero

_>0 : β€ β Type
(neg _) >0 = β₯
(posneg i) >0 = β₯
(pos zero) >0 = β₯
(pos (suc y)) >0 = Unit

isProp>0 : (y : β€) β isProp (y >0)
isProp>0 (pos (suc y)) = isPropUnit

>0-asym : (y : β€) β y >0 β (- y) >0 β β₯
>0-asym (pos (suc y)) _ p = p

>0-+ : (x y : β€) β x >0 β y >0 β (x + y) >0
>0-+ (pos (suc x)) (pos (suc y)) _ _ =
  subst (_>0) (signed-distrib spos (suc x) (suc y)) _

>0-Β· : (x y : β€) β x >0 β y >0 β (x Β· y) >0
>0-Β· (pos (suc x)) (pos (suc y)) _ _ =
  subst (_>0) (sym (Β·-signed-pos {s = spos} (suc x) (suc y))) _

trichotomy>0 : (x : β€) β Trichotomy>0 β€CommRing _>0 x
trichotomy>0 (neg (suc _)) = lt _
trichotomy>0 (signed spos zero) = eq refl
trichotomy>0 (signed sneg zero) = eq (sym posneg)
trichotomy>0 (posneg i) = eq (Ξ» j β posneg (i β§ ~ j))
trichotomy>0 (pos (suc _)) = gt _


{-

  β€ as ordered ring

-}

β€OrderedRing : OrderedRing _ _
β€OrderedRing = β€CommRing , orderstr _>0 isProp>0 _ >0-asym >0-+ >0-Β· trichotomy>0

open OrderedRingStr β€OrderedRing

βββββ€>0 : (n : βββ) β βββββ€ n > 0
βββββ€>0 n = transport (>0β‘>0r (βββββ€ n)) (helper n)
  where helper : (n : βββ) β βββββ€ n >0
        helper (1+ n) = _

-1Β·nβ‘-n : (n : β€) β -1 Β· n β‘ - n
-1Β·nβ‘-n n = helper1 1 n β (Ξ» i β - (Β·IdL n i))


possucn-1β‘1 : (n : β) β pos (suc n) - 1 β‘ pos n
possucn-1β‘1 n = +Comm (pos (suc n)) (- 1)

n>0βnβ₯1 : (n : β€) β n > 0 β n β₯ 1
n>0βnβ₯1 (pos (suc zero)) _ = inr refl
n>0βnβ₯1 n@(pos (suc (suc a))) _ = inl (subst (_>0) (sym (possucn-1β‘1 (suc a))) _)
n>0βnβ₯1 n@(neg (suc (suc _))) n>0 = Empty.rec (transport (sym (>0β‘>0r n)) n>0)

possucn>posn : (n : β) β pos (suc n) > pos n
possucn>posn n = subst (_>0) (sym possucn-posnβ‘1) _
  where possucn-posnβ‘1 : pos (suc n) - pos n β‘ 1
        possucn-posnβ‘1 = helper2 (pos (suc n)) (pos n) β (Ξ» i β possucn-1β‘1 n i + 1 - pos n) β helper3 (pos n)

n>0βposmβ‘n : (n : β€) β n > 0 β Ξ£[ m β β ] pos m β‘ n
n>0βposmβ‘n (pos n) _ = n , refl
n>0βposmβ‘n (neg n) n>0 = Empty.rec (transport (sym (>0β‘>0r (neg n))) n>0)


{-

  "Archimedean-ness" of β€

-}

archimedes : (a b : β€) β b > 0 β Ξ£[ n β β ] pos n Β· b > a
archimedes a (neg b) b>0 = Empty.rec (transport (sym (>0β‘>0r (neg b))) b>0)
archimedes a (pos b) b>0 with trichotomy a 0
... | lt a<0 = 1 , <-trans {x = a} {y = 0} {z = 1 Β· pos b} a<0 (subst (_> 0) (sym (Β·IdL (pos b))) b>0)
... | eq aβ‘0 = 1 , subst (1 Β· pos b >_) (sym aβ‘0) (subst (_> 0) (sym (Β·IdL (pos b))) b>0)
... | gt a>0 = suc an , subst (pos (suc an) Β· (pos b) >_) (Β·IdR a) posnΒ·b>aΒ·1
  where an = n>0βposmβ‘n a a>0 .fst
        p = n>0βposmβ‘n a a>0 .snd
        possucm>a : pos (suc an) > a
        possucm>a = subst (pos (suc an) >_) p (possucn>posn an)
        posnΒ·b>aΒ·1 : pos (suc an) Β· (pos b) > a Β· 1
        posnΒ·b>aΒ·1 = Β·-PosPres>β₯ {x = a} {y = pos (suc an)} a>0 _ possucm>a (n>0βnβ₯1 (pos b) b>0)

archimedes' : (a b : β€) β b > 0 β Ξ£[ n β β ] pos n Β· b + a > 0
archimedes' a b b>0 =
  let (n , posnΒ·b>-a) = archimedes (- a) b b>0
      posnΒ·b+a>-a+a : pos n Β· b + a > - a + a
      posnΒ·b+a>-a+a = +-rPres< {x = - a} {y = pos n Β· b} {z = a} posnΒ·b>-a
  in  n , subst (pos n Β· b + a >_) (+InvL a) posnΒ·b+a>-a+a
