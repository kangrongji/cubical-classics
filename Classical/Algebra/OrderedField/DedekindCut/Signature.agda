{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.DedekindCut.Signature where

open import Cubical.Foundations.Prelude


data Sign : Type where
  pos : Sign
  nul : Sign
  neg : Sign

-s_ : Sign → Sign
-s pos = neg
-s nul = nul
-s neg = pos

_·s_ : Sign → Sign → Sign
pos ·s x = x
nul ·s x = nul
neg ·s x = -s x

·s-Comm : (x y : Sign) → x ·s y ≡ y ·s x
·s-Comm pos pos = refl
·s-Comm nul pos = refl
·s-Comm neg pos = refl
·s-Comm pos nul = refl
·s-Comm nul nul = refl
·s-Comm neg nul = refl
·s-Comm pos neg = refl
·s-Comm nul neg = refl
·s-Comm neg neg = refl

·s-Assoc : (x y z : Sign) → x ·s (y ·s z) ≡  (x ·s y) ·s z
·s-Assoc nul _ _ = refl
·s-Assoc pos _ _ = refl
·s-Assoc neg pos pos = refl
·s-Assoc neg nul pos = refl
·s-Assoc neg neg pos = refl
·s-Assoc neg pos nul = refl
·s-Assoc neg nul nul = refl
·s-Assoc neg neg nul = refl
·s-Assoc neg pos neg = refl
·s-Assoc neg nul neg = refl
·s-Assoc neg neg neg = refl

·s-rUnit : (x : Sign) → x ·s pos ≡ x
·s-rUnit x = ·s-Comm x pos

-s-· : (x y : Sign) → (-s x) ·s y ≡ -s (x ·s y)
-s-· pos _ = refl
-s-· nul _ = refl
-s-· neg pos = refl
-s-· neg nul = refl
-s-· neg neg = refl
