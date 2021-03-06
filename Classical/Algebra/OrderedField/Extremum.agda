{-

Extremum, namely Supremum and Infimum of Subsets

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Extremum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (β ; zero ; suc)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Axioms
open import Classical.Preliminary.Logic
open import Classical.Foundations.Powerset
open import Classical.Algebra.OrderedField

private
  variable
    β β' : Level


module Extremum β¦ π€ : Oracle β¦ (π¦ : OrderedField β β') where

  open Oracle π€

  open OrderedFieldStr π¦

  private
      K = π¦ .fst .fst .fst

      variable
        p q : K


  {-

    Boundedness of Subsets

  -}

  isUpperBounded : β K β Type (β-max β β')
  isUpperBounded A = β₯ Ξ£[ b β K ] ((r : K) β r β A β r β€ b) β₯β

  isLowerBounded : β K β Type (β-max β β')
  isLowerBounded A = β₯ Ξ£[ b β K ] ((r : K) β r β A β b β€ r) β₯β


  {-

    Supremum and Infimum of Subsets

  -}

  record Supremum (A : β K) : Type (β-max β β') where
    field
      sup : K
      bound : (r : K) β r β A β r β€ sup
      least : (b : K) β ((r : K) β r β A β r β€ b) β b β₯ sup

  record Infimum (A : β K) : Type (β-max β β') where
    field
      inf : K
      bound : (r : K) β r β A β inf β€ r
      most  : (b : K) β ((r : K) β r β A β b β€ r) β b β€ inf

  open Supremum
  open Infimum


  -- Uniqueness of Extremum

  isPropSupremum : (A : β K) β isProp (Supremum A)
  isPropSupremum A s t i .sup = β€-asym (s .least _ (t .bound)) (t .least _ (s .bound)) i
  isPropSupremum A s t i .bound =
    isPropβPathP (Ξ» i β isPropΞ 2 (Ξ» r _ β isPropβ€ {x = r} {y = isPropSupremum A s t i .sup})) (s .bound) (t .bound) i
  isPropSupremum A s t i .least =
    isPropβPathP (Ξ» i β isPropΞ 2 (Ξ» b _ β isPropβ€ {x = isPropSupremum A s t i .sup} {y = b})) (s .least) (t .least) i

  isPropInfimum : (A : β K) β isProp (Infimum A)
  isPropInfimum A s t i .inf = β€-asym (t .most _ (s .bound)) (s .most _ (t .bound)) i
  isPropInfimum A s t i .bound =
    isPropβPathP (Ξ» i β isPropΞ 2 (Ξ» r _ β isPropβ€ {x = isPropInfimum A s t i .inf} {y = r})) (s .bound) (t .bound) i
  isPropInfimum A s t i .most  =
    isPropβPathP (Ξ» i β isPropΞ 2 (Ξ» b _ β isPropβ€ {x = b} {y = isPropInfimum A s t i .inf})) (s .most)  (t .most)  i


  {-

    Basic Properties

  -}

  <supβββ : {A : β K}(q : K)(boundary : Supremum A) β q < boundary .sup β β₯ Ξ£[ x β K ] (q < x) Γ (x β A) β₯β
  <supβββ {A = A} q boundary q<sup with decide (squashβ {A = Ξ£[ x β K ] (q < x) Γ (x β A)})
  ... | yes p = p
  ... | no Β¬p = Empty.rec (<β€-asym q<sup (boundary .least _ (Ξ» r rβA β case-split r (trichotomy q r) rβA)))
    where
    case-split : (x : K) β Trichotomy q x β x β A β x β€ q
    case-split _ (eq qβ‘x) _ = inr (sym qβ‘x)
    case-split _ (gt q>x) _ = inl q>x
    case-split x (lt q<x) xβA = Empty.rec (Β¬βΓβββΒ¬ (Ξ» _ β isProp<) (Ξ» _ β isPropβ A) Β¬p x q<x xβA)

  >supβΒ¬β : {A : β K}(q : K)(boundary : Supremum A) β q > boundary .sup β Β¬ q β A
  >supβΒ¬β {A = A} q boundary q>sup qβA with decide (isPropβ A)
  ... | yes qβA = <β€-asym q>sup (boundary .bound q qβA)
  ... | no Β¬qβA = Β¬qβA qβA

  ββsupβ€ : {A B : β K} β A β B β (SupA : Supremum A)(SupB : Supremum B) β SupA .sup β€ SupB .sup
  ββsupβ€ {A = A} {B = B} AβB SupA SupB = SupA .least _ (Ξ» r rβA β SupB .bound r (AβB rβA))


  >infβββ : {A : β K}(q : K)(boundary : Infimum A) β q > boundary .inf β β₯ Ξ£[ x β K ] (x < q) Γ (x β A) β₯β
  >infβββ {A = A} q boundary q>inf with decide (squashβ {A = Ξ£[ x β K ] (x < q) Γ (x β A)})
  ... | yes p = p
  ... | no Β¬p = Empty.rec (<β€-asym q>inf (boundary .most _ (Ξ» r rβA β case-split r (trichotomy q r) rβA)))
    where
    case-split : (x : K) β Trichotomy q x β x β A β q β€ x
    case-split _ (eq qβ‘x) _ = inr qβ‘x
    case-split _ (lt q<x) _ = inl q<x
    case-split x (gt q>x) xβA = Empty.rec (Β¬βΓβββΒ¬ (Ξ» _ β isProp<) (Ξ» _ β isPropβ A) Β¬p x q>x xβA)

  <infβΒ¬β : {A : β K}(q : K)(boundary : Infimum A) β q < boundary .inf β Β¬ q β A
  <infβΒ¬β {A = A} q boundary q<inf qβA with decide (isPropβ A)
  ... | yes qβA = <β€-asym q<inf (boundary .bound q qβA)
  ... | no Β¬qβA = Β¬qβA qβA


  -- By definition, if a subset admits extremum, it must be inhabited and bounded.

  SupβInhabited : {A : β K} β Supremum A β isInhabited A
  SupβInhabited {A = A} Sup with decide (isPropIsInhabited A)
  ... | yes qβA = qβA
  ... | no Β¬qβA = Empty.rec (<β€-asym q-1<q (Sup .least _ (allBound (Sup .sup - 1r))))
    where
    allBound : (x y : K) β y β A β y β€ x
    allBound x y yβA = Empty.rec (Β¬isInhabitedβΒ¬xβA Β¬qβA y yβA)

  SupβisUpperBounded : {A : β K} β Supremum A β isUpperBounded A
  SupβisUpperBounded Sup = β£ Sup .sup , Sup .bound β£β


  -- Supremum of { x | x β€ b } is just b itself.

  module _ (b : K) where

    prop-β€b : K β hProp _
    prop-β€b x = (x β€ b) , isPropβ€

    sub-β€b : β K
    sub-β€b = specify prop-β€b

    bβsub : b β sub-β€b
    bβsub = Inhabββ prop-β€b (inr refl)

    Supβ€b : Supremum sub-β€b
    Supβ€b .sup = b
    Supβ€b .bound r = ββInhab prop-β€b
    Supβ€b .least _ h = h _ bβsub

    Supβ€bβ‘b : (Sup : Supremum sub-β€b) β Sup .sup β‘ b
    Supβ€bβ‘b Sup i = isPropSupremum sub-β€b Sup Supβ€b i .sup


  -- If the subset is bounded by some element, its extremum is bounded by the same one.

  supUpperBounded : {A : β K}(b : K)(Sup : Supremum A) β ((x : K) β x β A β x β€ b) β Sup .sup β€ b
  supUpperBounded {A = A} b Sup bβ₯xβA = ββsupβ€ Aβ[xβ€b] Sup (Supβ€b b)
    where
    Aβ[xβ€b] : A β sub-β€b b
    Aβ[xβ€b] xβA = Inhabββ (prop-β€b b) (bβ₯xβA _ xβA)

  supLowerBounded : {A : β K}(b : K)(Sup : Supremum A) β ((x : K) β x β A β b β€ x) β Sup .sup β₯ b
  supLowerBounded b Sup bβ€xβA =
    Prop.rec isPropβ€ (Ξ» (x , xβA) β β€-trans (bβ€xβA x xβA) (Sup .bound x xβA)) (SupβInhabited Sup)


  {-

    Taking - x for all x β some subset and reverse its extremum

  -}

  module _ (A : β K) where

    -prop : K β hProp _
    -prop x = - x β A , isPropβ A

    -β : β K
    -β = specify -prop


  xβAβ-xβ-A : (A : β K){x : K} β x β A β - x β -β A
  xβAβ-xβ-A A {x = x} xβA = Inhabββ (-prop A) (subst (_β A) (sym (-Idempotent x)) xβA)

  -β-Idem : (A : β K) β -β (-β A) β‘ A
  -β-Idem A = biβββ‘ β-helper βhelper
    where
    β-helper : {x : K} β x β -β (-β A) β x β A
    β-helper {x = x} xβ =
      subst (_β A) (-Idempotent x) (ββInhab (-prop A) (ββInhab (-prop (-β A)) xβ))

    βhelper : {x : K} β x β A β x β -β (-β A)
    βhelper {x = x} xβ =
      Inhabββ (-prop (-β A)) (Inhabββ (-prop A) (subst (_β A) (sym (-Idempotent x)) xβ))


  isInhabited- : (A : β K) β isInhabited A β isInhabited (-β A)
  isInhabited- A = Prop.map (Ξ» (x , xβA) β - x , xβAβ-xβ-A A xβA)


  isUpperBoundedβisLowerBounded : (A : β K) β isUpperBounded A β isLowerBounded (-β A)
  isUpperBoundedβisLowerBounded A =
    Prop.map (Ξ» (b , bβ₯rβA) β - b , (Ξ» r rβ-A β -lReverseβ€ (bβ₯rβA _ (ββInhab (-prop A) rβ-A))))

  isLowerBoundedβisUpperBounded : (A : β K) β isLowerBounded A β isUpperBounded (-β A)
  isLowerBoundedβisUpperBounded A =
    Prop.map (Ξ» (b , bβ€rβA) β - b , (Ξ» r rβ-A β -rReverseβ€ (bβ€rβA _ (ββInhab (-prop A) rβ-A))))


  SupβInf- : (A : β K) β Supremum A β Infimum (-β A)
  SupβInf- A Sup .inf = - Sup .sup
  SupβInf- A Sup .bound r rβ-A = -lReverseβ€ (Sup .bound _ (ββInhab (-prop A) rβ-A))
  SupβInf- A Sup .most  b bβ€rβ-A = -rReverseβ€ (Sup .least _ -bβ₯rβ-A)
    where
    -bβ₯rβ-A : (r : K) β r β A β - b β₯ r
    -bβ₯rβ-A r rβA = -rReverseβ€ (bβ€rβ-A _ (xβAβ-xβ-A A rβA))

  InfβSup- : (A : β K) β Infimum A β Supremum (-β A)
  InfβSup- A Inf .sup = - Inf .inf
  InfβSup- A Inf .bound r rβ-A = -rReverseβ€ (Inf .bound _ (ββInhab (-prop A) rβ-A))
  InfβSup- A Inf .least b bβ₯rβ-A = -lReverseβ€ (Inf .most  _ -bβ€rβ-A)
    where
    -bβ€rβ-A : (r : K) β r β A β - b β€ r
    -bβ€rβ-A r rβA = -lReverseβ€ (bβ₯rβ-A _ (xβAβ-xβ-A A rβA))

  SupβInf : (A : β K) β Supremum (-β A) β Infimum A
  SupβInf A Sup = subst Infimum (-β-Idem A) (SupβInf- _ Sup)

  InfβSup : (A : β K) β Infimum (-β A) β Supremum A
  InfβSup A Sup = subst Supremum (-β-Idem A) (InfβSup- _ Sup)
