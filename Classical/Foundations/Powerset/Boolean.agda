{-

Boolean Algebraic Operations

This part doesn't need impredicativity actually.

-}
{-# OPTIONS --safe #-}
module Classical.Foundations.Powerset.Boolean where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms
open import Classical.Preliminary.Bool
open import Classical.Foundations.Powerset.Base
open import Classical.Foundations.Powerset.Membership

private
  variable
    β β' : Level
    X : Type β


module _ β¦ π€ : Oracle β¦ where


  {-

    Empty and Total Subset

  -}

  xββ : {x : X} β x β β
  xββ = refl

  xβtotal : {x : X} β x β total
  xβtotal = refl

  ββA : {A : β X} β β β A
  ββA xββ = Empty.rec (falseβ’true xββ)

  Aβtotal : {A : β X} β A β total
  Aβtotal _ = refl

  Aββ : {A : β X} β ((x : X) β x β A) β A β β
  Aββ p xβA = Empty.rec (trueβ’false (sym xβA β p _))

  totalβA : {A : β X} β ((x : X) β x β A) β total β A
  totalβA p _ = p _

  AβββAβ‘β : {A : β X} β A β β β A β‘ β
  AβββAβ‘β {A = A} Aββ = biβββ‘ Aββ (ββA {A = A})

  Aβ‘β : {A : β X} β ((x : X) β x β A) β A β‘ β
  Aβ‘β {A = A} p = AβββAβ‘β (Aββ p)

  Aβ‘total : {A : β X} β ((x : X) β x β A) β A β‘ total
  Aβ‘total {A = A} p = biβββ‘ (Aβtotal {A = A}) (totalβA p)

  Β¬xββ : (x : X) β x β β β β₯
  Β¬xββ x xββ = falseβ’true xββ


  {-

    Complement

  -}

  β-Unip : (A : β X) β β β A β‘ A
  β-Unip A i x = notnot (A x) i

  ββββ : {x : X}{A : β X} β x β A β x β (β A)
  ββββ xβA i = not (xβA i)

  ββββ : {x : X}{A : β X} β x β (β A) β x β A
  ββββ xββA = sym (notnot _) β cong not xββA


  {-

    Binary Union

  -}

  βͺ-lZero : (A : β X) β total βͺ A β‘ total
  βͺ-lZero A i x = zeroΛ‘ (A x) i

  βͺ-rZero : (A : β X) β A βͺ total β‘ total
  βͺ-rZero A i x = zeroΚ³ (A x) i

  βͺ-lUnit : (A : β X) β β βͺ A β‘ A
  βͺ-lUnit A i x = or-identityΛ‘ (A x) i

  βͺ-rUnit : (A : β X) β A βͺ β β‘ A
  βͺ-rUnit A i x = or-identityΚ³ (A x) i

  βͺ-Comm : (A B : β X) β A βͺ B β‘ B βͺ A
  βͺ-Comm A B i x = or-comm (A x) (B x) i

  βͺ-Assoc : (A B C : β X) β A βͺ (B βͺ C) β‘ (A βͺ B) βͺ C
  βͺ-Assoc A B C i x = or-assoc (A x) (B x) (C x) i

  βͺ-Idem : (A : β X) β A βͺ A β‘ A
  βͺ-Idem A i x = or-idem (A x) i

  βͺ-leftβ : {x : X}(A B : β X) β x β A β x β (A βͺ B)
  βͺ-leftβ {x = x} _ B xβA = (Ξ» i β xβA i or B x) β zeroΛ‘ _

  βͺ-rightβ : {x : X}(A B : β X) β x β B β x β (A βͺ B)
  βͺ-rightβ {x = x} A _ xβB = (Ξ» i β A x or xβB i) β zeroΚ³ _

  βͺ-leftβ : (A B : β X) β A β (A βͺ B)
  βͺ-leftβ A B = βͺ-leftβ A B

  βͺ-rightβ : (A B : β X) β B β (A βͺ B)
  βͺ-rightβ A B = βͺ-rightβ A B

  βAβͺBββA+βB : {x : X}(A B : β X) β x β (A βͺ B) β (x β A) β (x β B)
  βAβͺBββA+βB {x = x} A B xβAβͺB = or-dichotomy (A x) (B x) xβAβͺB

  βA+βBββAβͺB : {x : X}(A B : β X) β β₯ (x β A) β (x β B) β₯β β x β (A βͺ B)
  βA+βBββAβͺB {x = x} A B = Prop.rec (isPropβ (A βͺ B)) (Ξ» βA+βB β orβ‘true (A x) (B x) βA+βB)

  ββββͺ : {A B C : β X} β A β C β B β C β A βͺ B β C
  ββββͺ {A = A} {B = B} AβC BβC xβAβͺB with βAβͺBββA+βB A B xβAβͺB
  ... | inl xβA = AβC xβA
  ... | inr xβB = BβC xβB


  {-

    Binary Intersection

  -}

  β©-lZero : (A : β X) β β β© A β‘ β
  β©-lZero A i x = and-zeroΛ‘ (A x) i

  β©-rZero : (A : β X) β A β© β β‘ β
  β©-rZero A i x = and-zeroΚ³ (A x) i

  β©-lUnit : (A : β X) β total β© A β‘ A
  β©-lUnit A i x = and-identityΛ‘ (A x) i

  β©-rUnit : (A : β X) β A β© total β‘ A
  β©-rUnit A i x = and-identityΚ³ (A x) i

  β©-Comm : (A B : β X) β A β© B β‘ B β© A
  β©-Comm A B i x = and-comm (A x) (B x) i

  β©-Assoc : (A B C : β X) β A β© (B β© C) β‘ (A β© B) β© C
  β©-Assoc A B C i x = and-assoc (A x) (B x) (C x) i

  β©-Idem : (A : β X) β A β© A β‘ A
  β©-Idem A i x = and-idem (A x) i

  ββββ© : {x : X}(A B : β X) β x β A β x β B β x β (A β© B)
  ββββ© A B xβA xβB i = xβA i and xβB i

  ββββ© : {C : β X}(A B : β X) β C β A β C β B β C β (A β© B)
  ββββ© A B CβA CβB xβC = ββββ© A B (CβA xβC) (CβB xβC)

  leftβ-β© : {x : X}(A B : β X) β x β (A β© B) β x β A
  leftβ-β© {x = x} A B xβAβ©B = and-cancelΛ‘ (A x) (B x) xβAβ©B

  rightβ-β© : {x : X}(A B : β X) β x β (A β© B) β x β B
  rightβ-β© {x = x} A B xβAβ©B = and-cancelΚ³ (A x) (B x) xβAβ©B

  βββ©β : (A B C : β X) β A β B β (A β© C) β (B β© C)
  βββ©β A B C AβB xβAβ©C = ββββ© B C (AβB (leftβ-β© A C xβAβ©C)) (rightβ-β© A C xβAβ©C)

  AβB+Bβ©Cβ‘ββAβ©Cβ‘β : {A B C : β X} β A β B β B β© C β‘ β β A β© C β‘ β
  AβB+Bβ©Cβ‘ββAβ©Cβ‘β {A = A} {B = B} {C = C} AβB Bβ©Vβ‘β = AβββAβ‘β (subst ((A β© C) β_) Bβ©Vβ‘β (βββ©β A B C AβB))

  AβBβAβ©Bβ‘A : {A B : β X} β A β B β A β© B β‘ A
  AβBβAβ©Bβ‘A {A = A} {B = B} AβB = biβββ‘ (leftβ-β© A B) AβAβ©B
    where
    AβAβ©B : A β A β© B
    AβAβ©B xβA = ββββ© A B xβA (AβB xβA)


  {-

    Algebraic Laws of Boolean Algebra

  -}

  -- Absorption laws

  βͺ-β©-Absorp : (A B : β X) β A βͺ (A β© B) β‘ A
  βͺ-β©-Absorp A B i x = or-and-absorp (A x) (B x) i

  β©-βͺ-Absorp : (A B : β X) β A β© (A βͺ B) β‘ A
  β©-βͺ-Absorp A B i x = and-or-absorp (A x) (B x) i


  -- Distribution laws

  βͺ-β©-rDist : (A B C : β X) β A βͺ (B β© C) β‘ (A βͺ B) β© (A βͺ C)
  βͺ-β©-rDist A B C i x = or-and-dist (A x) (B x) (C x) i

  β©-βͺ-rDist : (A B C : β X) β A β© (B βͺ C) β‘ (A β© B) βͺ (A β© C)
  β©-βͺ-rDist A B C i x = and-or-dist (A x) (B x) (C x) i

  βͺ-β©-lDist : (A B C : β X) β (A β© B) βͺ C β‘ (A βͺ C) β© (B βͺ C)
  βͺ-β©-lDist A B C = βͺ-Comm _ _ β βͺ-β©-rDist _ _ _ β (Ξ» i β βͺ-Comm C A i β© βͺ-Comm C B i)

  β©-βͺ-lDist : (A B C : β X) β (A βͺ B) β© C β‘ (A β© C) βͺ (B β© C)
  β©-βͺ-lDist A B C = β©-Comm _ _ β β©-βͺ-rDist _ _ _ β (Ξ» i β β©-Comm C A i βͺ β©-Comm C B i)


  -- Complementation laws

  βͺ-Compt : (A : β X) β A βͺ (β A) β‘ total
  βͺ-Compt A i x = or-compt (A x) i

  β©-Compt : (A : β X) β A β© (β A) β‘ β
  β©-Compt A i x = and-compt (A x) i


  -- de Morgan laws

  βͺ-β©-deMorgan : (A B : β X) β (β A) βͺ (β B) β‘ β (A β© B)
  βͺ-β©-deMorgan A B i x = or-and-deMorgan (A x) (B x) i

  β©-βͺ-deMorgan : (A B : β X) β (β A) β© (β B) β‘ β (A βͺ B)
  β©-βͺ-deMorgan A B i x = and-or-deMorgan (A x) (B x) i


  {-

    Facts relating non-intersecting subsets and complementary subsets

  -}

  ββ©β : {A B : β X} β ((x : X) β x β A β x β B) β A β© B β‘ β
  ββ©β {A = A} {B = B} p i x with dichotomyβ x A
  ... | yeah xβA = xβA i and p x xβA i
  ... | nope xβA = and-absorpΛ‘ (A x) (B x) xβA i

  ββ©β' : {A B : β X} β ((x : X) β x β A β x β B β β₯) β A β© B β‘ β
  ββ©β' {B = B} p = ββ©β (Ξ» x xβA β Β¬βββ {A = B} (p x xβA))

  Aβ©B=ββAββB : {A B : β X} β A β© B β‘ β β A β (β B)
  Aβ©B=ββAββB {A = A} {B = B} Aβ©Bβ‘β {x = x} xβA =
    ββββ {A = B} (and-forceΛ‘ (A x) (B x) (Ξ» i β Aβ©Bβ‘β i x) xβA)

  Aβ©B=ββBββA : {A B : β X} β A β© B β‘ β β B β (β A)
  Aβ©B=ββBββA Aβ©Bβ‘β = Aβ©B=ββAββB (β©-Comm _ _ β Aβ©Bβ‘β)

  AββBβAβ©B=β : {A B : β X} β A β (β B) β A β© B β‘ β
  AββBβAβ©B=β {X = X} {A = A} {B = B} AββB = ββ©β helper
    where
    helper : (x : X) β x β A β x β B
    helper x xβA = ββββ {A = B} (AββB xβA)

  BββAβAβ©B=β : {A B : β X} β B β (β A) β A β© B β‘ β
  BββAβAβ©B=β BββA = β©-Comm _ _ β AββBβAβ©B=β BββA


  {-

    Specification and algebraic operations

  -}

  module _
    (P : X β hProp β)(Q : X β hProp β') where

    β-βͺβInhabβ : (x : X) β x β specify P βͺ specify Q β P x .fst β Q x .fst
    β-βͺβInhabβ x xββͺ with βAβͺBββA+βB (specify P) (specify Q) xββͺ
    ... | inl p = inl (ββInhab P p)
    ... | inr q = inr (ββInhab Q q)

    Inhabβββ-βͺ : (x : X) β β₯ P x .fst β Q x .fst β₯β β x β specify P βͺ specify Q
    Inhabβββ-βͺ x =
      Prop.rec (isPropβ (specify P βͺ specify Q))
      (Ξ» { (inl p) β βͺ-leftβ  (specify P) (specify Q) (Inhabββ P p)
         ; (inr q) β βͺ-rightβ (specify P) (specify Q) (Inhabββ Q q) })
