{-# OPTIONS --safe #-}
module Classical.Algebra.Field.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Nullary

private
  variable
    β  : Level


module _ (π‘ : CommRing β) where

  open CommRingStr (π‘ .snd)
  open Units        π‘

  private
    R = π‘ .fst

  isField : Type β
  isField = (x : R) β Β¬ x β‘ 0r β Ξ£[ y β R ] x Β· y  β‘ 1r

  isPropIsField : isProp isField
  isPropIsField = isPropΞ 2 (Ξ» x _ β inverseUniqueness x)


Field : (β : Level) β Type (β-suc β)
Field β = Ξ£[ π‘ β CommRing β ] isField π‘


liftPathIsField : {π‘ π‘' : CommRing β}(p : π‘ β‘ π‘')(h : isField π‘)(h' : isField π‘') β PathP (Ξ» i β isField (p i)) h h'
liftPathIsField p = isPropβPathP (Ξ» i β isPropIsField (p i))
