{-

Classical Impredicative Powerset

This file introduces a "powerset", thanks to Excluded Middle,
behaving very similar to that in classical set theory.
However, I think except for a few `Boolean facts`,
most of the following results only relies on the concept of impredicativity,
and one way to formulate that is the existence of subobject classifier
(LEM or even Propostional Resizing is enough to guarantee its existence).

Stuffs about powerset are separated into several files in this fold.

This one is classical and impredicative.
One can find a constructive and predicative version in the standard library of Cubical Agda,
see "https://github.com/agda/cubical/blob/master/Cubical/Foundations/Powerset.agda".

-}
{-# OPTIONS --safe #-}
module Classical.Foundations.Powerset.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool

open import Classical.Axioms
open import Classical.Foundations.Prelude

private
  variable
    β : Level
    X : Type β


module _ β¦ π€ : Oracle β¦ where

  open Oracle π€


  -- The powerset construction, namely the type of all possible "subsets",
  -- well-behaved only when one has some kind of impredicativity.

  β_ : Type β β Type β
  β X = X β Prop

  isSetβ : isSet (β X)
  isSetβ = isSetΞ  Ξ» _ β isSetProp


  -- The specification operator `specify`,
  -- transforming a predicate into the subset of elements that satisfying it,
  -- in certain sense realizes the axiom of specification/separation in classical set theory.

  specify : {β : Level} β (X β hProp β) β β X
  specify P x = bool (decide (P x .snd))


  -- The Mmpty Subset

  β : β X
  β x = false

  -- The Total Subset

  total : β X
  total x = true


  -- Membership Relation

  _β_ : X β β X β Type
  x β A = A x β‘ true

  infix 6 _β_

  isPropβ : {x : X}(A : β X) β isProp (x β A)
  isPropβ _ = isSetProp _ _

  -- Non-Membership

  _β_ : X β β X β Type
  x β A = A x β‘ false

  infix 6 _β_

  isPropβ : {x : X}(A : β X) β isProp (x β A)
  isPropβ _ = isSetProp _ _

  -- Inclusion Relation of Subsets

  _β_ : {X : Type β} β β X β β X β Type β
  A β B = β {x} β x β A β x β B

  infix 7 _β_

  isPropβ : {A B : β X} β isProp (A β B)
  isPropβ {B = B} = isPropImplicitΞ  (Ξ» x β isPropΞ  (Ξ» _ β isPropβ B))


  -- Complement of Subset

  β_ : β X β β X
  (β P) x = not (P x)

  infixr 10 β_

  -- Binary Union

  _βͺ_ : β X β β X β β X
  (A βͺ B) x = A x or B x

  infixr 8 _βͺ_

  -- Binary Intersection

  _β©_ : β X β β X β β X
  (A β© B) x = A x and B x

  infixr 9 _β©_
