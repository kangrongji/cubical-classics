{-

Multiplicative Structure on Dedekind Cuts

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Algebra.OrderedField.DedekindCut.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing

open import Classical.Axioms
open import Classical.Foundations.Powerset

open import Classical.Algebra.Field
open import Classical.Algebra.OrderedRing
open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.DedekindCut.Base
open import Classical.Algebra.OrderedField.DedekindCut.Algebra
open import Classical.Algebra.OrderedField.DedekindCut.Signature
open import Classical.Algebra.OrderedField.DedekindCut.Order

private
  variable
    β β' : Level


module Multiplication β¦ π€ : Oracle β¦
  (π¦ : OrderedField β β')(archimedes : isArchimedean (π¦ . fst))
  where

  private
    K = π¦ .fst .fst .fst

  open OrderedFieldStr π¦
  open Basics   π¦
  open Algebra  π¦ archimedes
  open Order    π¦ archimedes
  open DedekindCut


  {-

    Full Multiplication

  -}

  _Β·π_ : π β π β π
  (a Β·π b) = signed (sign a Β·s sign b) (absπ a Β·πβ absπ b)


  private
    lZeroSign : (a : π) β sign π β‘ sign π Β·s sign a
    lZeroSign a = signπ β (Ξ» i β signπ (~ i) Β·s sign a)

    rZeroSign : (a : π) β sign π β‘ sign a Β·s sign π
    rZeroSign a = lZeroSign a β Β·s-Comm (sign π) (sign a)

    lZero : (a : π) β absπ π β‘ absπ π Β·πβ absπ a
    lZero a = absπ β sym (Β·πβZeroL (absπ a)) β (Ξ» i β absπ (~ i) Β·πβ absπ a)

    rZero : (a : π) β absπ π β‘ absπ a Β·πβ absπ π
    rZero a = lZero a β Β·πβComm (absπ π) (absπ a)

  signΒ· : (a b : π) β sign (a Β·π b) β‘ sign a Β·s sign b
  signΒ· a b = case-split (trichotomyπ a π) (trichotomyπ b π)
    where
    case-split : Trichotomyπ a π β Trichotomyπ b π β sign (a Β·π b) β‘ sign a Β·s sign b
    case-split (gt a>0) (gt b>0) =
      sign-signed _ (absπ a Β·πβ absπ b) (>π-arefl (Β·π-Pres>0 (absπ a) (absπ b) (abs>0 a a>0) (abs>0 b b>0)))
    case-split (lt a<0) (lt b<0) =
      sign-signed _ (absπ a Β·πβ absπ b) (>π-arefl (Β·π-Pres>0 (absπ a) (absπ b) (abs<0 a a<0) (abs<0 b b<0)))
    case-split (gt a>0) (lt b<0) =
      sign-signed _ (absπ a Β·πβ absπ b) (>π-arefl (Β·π-Pres>0 (absπ a) (absπ b) (abs>0 a a>0) (abs<0 b b<0)))
    case-split (lt a<0) (gt b>0) =
      sign-signed _ (absπ a Β·πβ absπ b) (>π-arefl (Β·π-Pres>0 (absπ a) (absπ b) (abs<0 a a<0) (abs>0 b b>0)))
    case-split (eq aβ‘0) _ =
      (Ξ» i β sign (signed (signβ‘0 a aβ‘0 i Β·s sign b) (absπ a Β·πβ absπ b)))
      β lZeroSign b β (Ξ» i β sign (aβ‘0 (~ i)) Β·s sign b)
    case-split _ (eq bβ‘0) =
      (Ξ» i β sign (signed (sign a Β·s signβ‘0 b bβ‘0 i) (absπ a Β·πβ absπ b)))
      β (Ξ» i β sign (signed (Β·s-Comm (sign a) nul i) (absπ a Β·πβ absπ b)))
      β rZeroSign a β (Ξ» i β sign a Β·s sign (bβ‘0 (~ i)))

  absΒ· : (a b : π) β absπ (a Β·π b) β‘ (absπ a Β·πβ absπ b)
  absΒ· a b = case-split (trichotomyπ a π) (trichotomyπ b π)
    where
    case-split : Trichotomyπ a π β Trichotomyπ b π β absπ (a Β·π b) β‘ (absπ a Β·πβ absπ b)
    case-split (gt a>0) (gt b>0) =
      (Ξ» i β absπ (signed (sign>0 a a>0 i Β·s sign>0 b b>0 i) (absπ a Β·πβ absπ b)))
      β abs-signed _ _ posβ’nul
    case-split (lt a<0) (lt b<0) =
      (Ξ» i β absπ (signed (sign<0 a a<0 i Β·s sign<0 b b<0 i) (absπ a Β·πβ absπ b)))
      β abs-signed _ _ posβ’nul
    case-split (gt a>0) (lt b<0) =
      (Ξ» i β absπ (signed (sign>0 a a>0 i Β·s sign<0 b b<0 i) (absπ a Β·πβ absπ b)))
      β abs-signed _ _ negβ’nul
    case-split (lt a<0) (gt b>0) =
      (Ξ» i β absπ (signed (sign<0 a a<0 i Β·s sign>0 b b>0 i) (absπ a Β·πβ absπ b)))
      β abs-signed _ _ negβ’nul
    case-split (eq aβ‘0) _ =
      (Ξ» i β absπ (signed (signβ‘0 a aβ‘0 i Β·s sign b) (absπ a Β·πβ absπ b)))
      β lZero b β (Ξ» i β absπ (aβ‘0 (~ i)) Β·πβ absπ b)
    case-split _ (eq bβ‘0) =
      (Ξ» i β absπ (signed (sign a Β·s signβ‘0 b bβ‘0 i) (absπ a Β·πβ absπ b)))
      β (Ξ» i β absπ (signed (Β·s-Comm (sign a) nul i) (absπ a Β·πβ absπ b)))
      β rZero a β (Ξ» i β absπ a Β·πβ absπ (bβ‘0 (~ i)))


  Β·πComm : (a b : π) β a Β·π b β‘ b Β·π a
  Β·πComm a b i = signed (Β·s-Comm (sign a) (sign b) i) (Β·πβComm (absπ a) (absπ b) i)

  Β·πAssoc : (a b c : π) β a Β·π (b Β·π c) β‘ (a Β·π b) Β·π c
  Β·πAssoc a b c =
    let p = Ξ» i β signed (sign a Β·s signΒ· b c i) (absπ a Β·πβ absΒ· b c i)
        q = Ξ» i β signed (signΒ· a b i Β·s sign c) (absΒ· a b i Β·πβ absπ c)
        r = Ξ» i β signed (Β·s-Assoc (sign a) (sign b) (sign c) i) (Β·πβAssoc (absπ a) (absπ b) (absπ c) i)
    in  p β r β sym q


  Β·πIdR : (a : π) β a Β·π π β‘ a
  Β·πIdR a = (Ξ» i β signed (sign-path i) (absπ a Β·πβ absπ i))
    β (Ξ» i β signed (sign a) (Β·πβIdR (absπ a) i))
    β sign-abs-β‘ a
    where
    sign-path : sign a Β·s sign π β‘ sign a
    sign-path = (Ξ» i β sign a Β·s signπ i) β Β·s-rUnit (sign a)

  Β·πZeroR : (a : π) β a Β·π π β‘ π
  Β·πZeroR a = (Ξ» i β signed (sign a Β·s sign π) (absπ a Β·πβ absπ i))
    β (Ξ» i β signed (sign a Β·s sign π) (Β·πβZeroR (absπ a) i))
    β signedπ (sign a Β·s sign π)

  Β·πZeroL : (a : π) β π Β·π a β‘ π
  Β·πZeroL a = Β·πComm π a β Β·πZeroR a


  neg-Β·π : (a b : π) β ((-π a) Β·π b) β‘ -π (a Β·π b)
  neg-Β·π  a b = (Ξ» i β signed (-sign a i Β·s sign b) (abs-π a i Β·πβ absπ b))
    β (Ξ» i β signed (-s-Β· (sign a) (sign b) i) (absπ a Β·πβ absπ b))
    β signed- (sign a Β·s sign b) (absπ a Β·πβ absπ b)

  Β·π-neg : (a b : π) β (a Β·π (-π b)) β‘ -π (a Β·π b)
  Β·π-neg a b = Β·πComm a (-π b) β neg-Β·π b a β cong (-π_) (Β·πComm b a)

  neg-Β·π-neg : (a b : π) β ((-π a) Β·π (-π b)) β‘ a Β·π b
  neg-Β·π-neg a b = neg-Β·π a (-π b) β cong (-π_) (Β·π-neg a b) β -πInvolutive (a Β·π b)


  private
    Β·pos-helper : (a b : π) β a β₯π π β b β₯π π β a Β·π b β‘ ((absπ a) Β·πβ (absπ b)) .fst
    Β·pos-helper a b aβ₯0 bβ₯0 = case-split (trichotomyπ a π) (trichotomyπ b π)
      where
      case-split : Trichotomyπ a π β Trichotomyπ b π β a Β·π b β‘ ((absπ a) Β·πβ (absπ b)) .fst
      case-split (lt a<0) _ = Empty.rec (<β€π-asym a π a<0 aβ₯0)
      case-split _ (lt b<0) = Empty.rec (<β€π-asym b π b<0 bβ₯0)
      case-split (eq aβ‘0) _ =
          (Ξ» i β aβ‘0 i Β·π b)
        β Β·πZeroL b
        β (Ξ» i β (Β·πβZeroL (absπ b) (~ i)) .fst)
        β (Ξ» i β (absπ (~ i) Β·πβ (absπ b)) .fst)
        β (Ξ» i β (absπ (aβ‘0 (~ i)) Β·πβ (absπ b)) .fst)
      case-split _ (eq bβ‘0) =
        (Ξ» i β a Β·π bβ‘0 i)
        β Β·πZeroR a
        β (Ξ» i β (Β·πβZeroR (absπ a) (~ i)) .fst)
        β (Ξ» i β ((absπ a) Β·πβ absπ (~ i)) .fst)
        β (Ξ» i β ((absπ a) Β·πβ absπ (bβ‘0 (~ i))) .fst)
      case-split (gt a>0) (gt b>0) i =
        signed ((sign>0 a a>0 i) Β·s(sign>0 b b>0 i)) ((absπ a) Β·πβ (absπ b))

    +pos-helper : (a b : π) β a β₯π π β b β₯π π β absπ (a +π b) β‘ ((absπ a) +πβ (absπ b))
    +pos-helper a b aβ₯0 bβ₯0 = path-πβ (absπ (a +π b)) _ path
      where a+bβ₯0 : (a +π b) β₯π π
            a+bβ₯0 = +π-Presβ₯0 a b aβ₯0 bβ₯0
            path : absπ (a +π b) .fst β‘ ((absπ a) +πβ (absπ b)) .fst
            path = absβ₯0 (a +π b) a+bβ₯0 β (Ξ» i β absβ₯0 a aβ₯0 (~ i) +π absβ₯0 b bβ₯0 (~ i))

  Β·πDistR-PosPosPos : (a b c : π)
    β a β₯π π β b β₯π π β c β₯π π
    β (a Β·π b) +π (a Β·π c) β‘ a Β·π (b +π c)
  Β·πDistR-PosPosPos a b c aβ₯0 bβ₯0 cβ₯0 =
      (Ξ» i β Β·pos-helper a b aβ₯0 bβ₯0 i +π Β·pos-helper a c aβ₯0 cβ₯0 i)
    β (Ξ» i β Β·πβDistR (absπ a) (absπ b) (absπ c) i .fst)
    β (Ξ» i β ((absπ a) Β·πβ +pos-helper b c bβ₯0 cβ₯0 (~ i)) .fst)
    β sym (Β·pos-helper a (b +π c) aβ₯0 b+cβ₯0)
    where
    b+cβ₯0 : (b +π c) β₯π π
    b+cβ₯0 = +π-Presβ₯0 b c bβ₯0 cβ₯0

  Β·πDistR-PosPosNeg : (a b c : π)
    β a β₯π π β b β₯π π β c <π π β (b +π c) β₯π π
    β (a Β·π b) +π (a Β·π c) β‘ a Β·π (b +π c)
  Β·πDistR-PosPosNeg a b c aβ₯0 bβ₯0 c<0 b+cβ₯0 = (Ξ» i β path1 (~ i) +π (a Β·π c)) β path2
    where
    path1 : (a Β·π (b +π c)) +π (-π (a Β·π c)) β‘ a Β·π b
    path1 = (Ξ» i β (a Β·π (b +π c)) +π Β·π-neg a c (~ i))
      β Β·πDistR-PosPosPos a (b +π c) (-π c) aβ₯0 b+cβ₯0 (<0-reverse c c<0)
      β (Ξ» i β a Β·π +πAssoc b c (-π c) (~ i))
      β (Ξ» i β a Β·π (b +π +πInvR c i)) β (Ξ» i β a Β·π (+πIdR b i))
    path2 : ((a Β·π (b +π c)) +π (-π (a Β·π c))) +π (a Β·π c) β‘ a Β·π (b +π c)
    path2 = sym (+πAssoc _ _ _) β (Ξ» i β (a Β·π (b +π c)) +π +πInvL (a Β·π c) i) β +πIdR _

  Β·πDistR-PosPos : (a b c : π)
    β a β₯π π β (b +π c) β₯π π
    β (a Β·π b) +π (a Β·π c) β‘ a Β·π (b +π c)
  Β·πDistR-PosPos a b c aβ₯0 b+cβ₯0 = case-split (dichotomyπ b π) (dichotomyπ c π)
    where
    case-split : Dichotomyπ b π β Dichotomyπ c π β (a Β·π b) +π (a Β·π c) β‘ a Β·π (b +π c)
    case-split (ge bβ₯0) (ge cβ₯0) = Β·πDistR-PosPosPos a b c aβ₯0 bβ₯0 cβ₯0
    case-split (lt b<0) (ge cβ₯0) = +πComm _ _
      β (Ξ» i β Β·πDistR-PosPosNeg a c b aβ₯0 cβ₯0 b<0 c+bβ₯0 i)
      β (Ξ» i β a Β·π +πComm c b i)
      where c+bβ₯0 : (c +π b) β₯π π
            c+bβ₯0 = subst (_β₯π π) (+πComm b c) b+cβ₯0
    case-split (ge bβ₯0) (lt c<0) = Β·πDistR-PosPosNeg a b c aβ₯0 bβ₯0 c<0 b+cβ₯0
    case-split (lt b<0) (lt c<0) = Empty.rec (<β€π-asym (b +π c) π (+π-Pres<0 b c b<0 c<0) b+cβ₯0)

  private
    alg-helper' : (a b c d : π) β (a +π b) +π (c +π d) β‘ (a +π c) +π (b +π d)
    alg-helper' a b c d = +πAssoc (a +π b) c d
      β (Ξ» i β +πAssoc a b c (~ i) +π d)
      β (Ξ» i β (a +π +πComm b c i) +π d)
      β (Ξ» i β +πAssoc a c b i +π d)
      β sym (+πAssoc (a +π c) b d)

    alg-helper : (a b : π) β -π (a +π b) β‘ (-π a) +π (-π b)
    alg-helper a b = sym (+πIdR (-π (a +π b)))
      β (Ξ» i β (-π (a +π b)) +π path (~ i))
      β +πAssoc _ _ _
      β (Ξ» i β +πInvL (a +π b) i +π ((-π a) +π (-π b)))
      β +πIdL ((-π a) +π (-π b))
      where
      path : (a +π b) +π ((-π a) +π (-π b)) β‘ π
      path = alg-helper' _ _ _ _ β (Ξ» i β +πInvR a i +π +πInvR b i) β +πIdR π

  Β·πDistR-NegPos : (a b c : π)
    β a <π π β (b +π c) β₯π π
    β (a Β·π b) +π (a Β·π c) β‘ a Β·π (b +π c)
  Β·πDistR-NegPos a b c a<0 b+cβ₯0 =
    sym (-πInvolutive _) β (Ξ» i β -π path i) β -πInvolutive _
    where
    path : -π ((a Β·π b) +π (a Β·π c)) β‘ -π (a Β·π (b +π c))
    path = alg-helper (a Β·π b) (a Β·π c)
      β (Ξ» i β neg-Β·π a b (~ i) +π neg-Β·π a c (~ i))
      β Β·πDistR-PosPos (-π a) b c (<0-reverse a a<0) b+cβ₯0
      β neg-Β·π a (b +π c)

  Β·πDistR-Pos : (a b c : π)
    β (b +π c) β₯π π
    β (a Β·π b) +π (a Β·π c) β‘ a Β·π (b +π c)
  Β·πDistR-Pos a b c b+cβ₯0 = case-split (dichotomyπ a π)
    where
    case-split : Dichotomyπ a π β (a Β·π b) +π (a Β·π c) β‘ a Β·π (b +π c)
    case-split (ge aβ₯0) = Β·πDistR-PosPos a b c aβ₯0 b+cβ₯0
    case-split (lt a<0) = Β·πDistR-NegPos a b c a<0 b+cβ₯0

  Β·πDistR-Neg : (a b c : π)
    β (b +π c) <π π
    β (a Β·π b) +π (a Β·π c) β‘ a Β·π (b +π c)
  Β·πDistR-Neg a b c b+c<0 =
    sym (-πInvolutive _) β (Ξ» i β -π path i) β -πInvolutive _
    where
    -b+-kβ₯0 : ((-π b) +π (-π c)) β₯π π
    -b+-kβ₯0 = subst (_β₯π π) (alg-helper b c) (<0-reverse (b +π c) b+c<0)
    path : -π ((a Β·π b) +π (a Β·π c)) β‘ -π (a Β·π (b +π c))
    path = alg-helper (a Β·π b) (a Β·π c)
      β (Ξ» i β Β·π-neg a b (~ i) +π Β·π-neg a c (~ i))
      β Β·πDistR-Pos a (-π b) (-π c) -b+-kβ₯0
      β (Ξ» i β a Β·π alg-helper b c (~ i))
      β Β·π-neg a (b +π c)

  Β·πDistR : (a b c : π) β (a Β·π b) +π (a Β·π c) β‘ a Β·π (b +π c)
  Β·πDistR a b c = case-split (dichotomyπ (b +π c) π)
    where
    case-split : Dichotomyπ (b +π c) π β (a Β·π b) +π (a Β·π c) β‘ a Β·π (b +π c)
    case-split (ge b+cβ₯0) = Β·πDistR-Pos a b c b+cβ₯0
    case-split (lt b+c<0) = Β·πDistR-Neg a b c b+c<0


  -- The previously defined _Β·πβ_ is equal to _Β·π_ when both variables are non-negative.

  Β·πβ‘Β·πβ : (a b : πβ) β a .fst Β·π b .fst β‘ (a Β·πβ b) .fst
  Β·πβ‘Β·πβ (a , aβ₯0) (b , bβ₯0) = Β·pos-helper a b aβ₯0 bβ₯0
    β (Ξ» i β (path-πβ (absπ a) (a , aβ₯0) (absβ₯0 a aβ₯0) i
          Β·πβ path-πβ (absπ b) (b , bβ₯0) (absβ₯0 b bβ₯0) i) .fst)


  {-

    Commutative Ring Instance

  -}

  πCommRing : CommRing (β-max β β')
  πCommRing = makeCommRing {R = π}
      π π _+π_ _Β·π_ -π_ isSetπ
    +πAssoc +πIdR +πInvR +πComm
    Β·πAssoc Β·πIdR (Ξ» x y z β sym (Β·πDistR x y z)) Β·πComm


  {-

    Ordered Ring Instance

  -}

  private
    Β·π-Pos-helper : (a b : π) β a >π π β b >π π β ((absπ a) Β·πβ (absπ b)) .fst β‘ a Β·π b
    Β·π-Pos-helper a b a>0 b>0 = sym (Β·pos-helper a b (<πββ€π {a = π} {b = a} a>0) (<πββ€π {a = π} {b = b} b>0))

  Β·π'-Pres>0 : (a b : π) β a >π π β b >π π β (a Β·π b) >π π
  Β·π'-Pres>0 a b a>0 b>0 =
    subst (_>π π) (Β·π-Pos-helper a b a>0 b>0) (Β·π-Pres>0 (absπ a) (absπ b) (abs>0 a a>0) (abs>0 b b>0))

  trichotomy>π0 : (a : π) β Trichotomy>0 πCommRing (_>π π) a
  trichotomy>π0 a = case-split (trichotomyπ a π)
    where
    case-split : Trichotomyπ a π β _
    case-split (lt a<0) = lt (-reverse<0 a a<0)
    case-split (eq aβ‘0) = eq aβ‘0
    case-split (gt a>0) = gt a>0


  πOrderedRing : OrderedRing (β-max β β') (β-max β β')
  πOrderedRing = πCommRing ,
    orderstr
      (_>π π) (Ξ» a β isProp<π {a = π} {b = a}) 1>π0
      (Ξ» a β a>0+-a>0ββ₯ {a = a}) +π-Pres>0
      Β·π'-Pres>0 trichotomy>π0


  -- The ordering given by general theory of oredered ring is same as the one used here before

  open OrderedRingStr πOrderedRing using ()
    renaming (_<_ to _<π'_ ; _>_ to _>π'_ ; _β€_ to _β€π'_ ; _β₯_ to _β₯π'_)

  <πβ<π' : (a b : π) β a <π b β a <π' b
  <πβ<π' a b a<b = subst ((b +π (-π a)) >π_) (+πInvR a) (+π-rPres< a b (-π a) a<b)

  <π'β<π : (a b : π) β a <π' b β a <π b
  <π'β<π a b 0<b-a = transport (Ξ» i β +πIdL a i <π b-a+bβ‘b i) (+π-rPres< π (b +π (-π a)) a 0<b-a)
    where b-a+bβ‘b : (b +π (-π a)) +π a β‘ b
          b-a+bβ‘b = sym (+πAssoc _ _ _) β (Ξ» i β b +π +πInvL a i) β +πIdR b

  β€πββ€π' : (a b : π) β a β€π b β a β€π' b
  β€πββ€π' a b aβ€b with splitβ€π a b aβ€b
  ... | lt a<b = inl (<πβ<π' a b a<b)
  ... | eq aβ‘b = inr aβ‘b

  β€π'ββ€π : (a b : π) β a β€π' b β a β€π b
  β€π'ββ€π a b (inl a<b') = <πββ€π {a = a} {b = b} (<π'β<π a b a<b')
  β€π'ββ€π a b (inr aβ‘b ) = β€π-refl aβ‘b


  {-

    Multiplicative Inverse

  -}

  isInvπβ : (a : πβ) β Type (β-max β β')
  isInvπβ a =  Ξ£[ a' β πβ ] (a Β·πβ a') .fst β‘ π

  isPropIsInv : (a : πβ) β isProp (isInvπβ a)
  isPropIsInv a (x , p) (y , q) i .fst = xβ‘y i
    where
    xβ‘y : x β‘ y
    xβ‘y = sym (Β·πβIdR x)
      β (Ξ» i β x Β·πβ path-πβ (a Β·πβ y) πβ q (~ i))
      β Β·πβAssoc x a y
      β (Ξ» i β Β·πβComm x a i Β·πβ y)
      β (Ξ» i β path-πβ (a Β·πβ x) πβ p i Β·πβ y)
      β Β·πβIdL y
  isPropIsInv a u@(x , p) v@(y , q) i .snd j =
    isSetβSquareP (Ξ» _ _ β isSetπ) p q
      (Ξ» i β (a Β·πβ isPropIsInv a u v i .fst) .fst) refl i j

  Β·πβInvR : (a : πβ) β a .fst >π π β isInvπβ a
  Β·πβInvR a = Prop.rec (isPropIsInv a)
    (Ξ» (q , q<rβa , qβπ) β
      let q>0 = qβπββq>0 πβ q qβπ in
      invπβ (a .fst) q q>0 q<rβa , Β·πβInvR' a q q>0 q<rβa)

  invπβ>0 : (a : πβ)(aβ»ΒΉ : isInvπβ a) β aβ»ΒΉ .fst .fst >π π
  invπβ>0 a ((a' , a'β₯0) , p) with splitβ€π π a' a'β₯0
  ... | lt 0<a' = 0<a'
  ... | eq 0β‘a' = Empty.rec (<π-arefl 1>π0 πβ‘π)
    where πβ‘π : π β‘ π
          πβ‘π = (Ξ» i β Β·πβZeroR a (~ i) .fst)
            β (Ξ» i β (a Β·πβ path-πβ πβ (a' , a'β₯0) 0β‘a' i) .fst) β p


  isInvπ : (a : π) β Type (β-max β β')
  isInvπ a = Ξ£[ a' β π ] a Β·π a' β‘ π

  module _ (a : π)(a>0 : a >π π) where

    private
      aβ : πβ
      aβ = a , <πββ€π {a = π} {b = a} a>0
      Ξ£aβ»ΒΉ = Β·πβInvR aβ a>0
      aββ»ΒΉ = Ξ£aβ»ΒΉ .fst
      aβ»ΒΉ = Ξ£aβ»ΒΉ .fst .fst
      aβ»ΒΉ>0 = invπβ>0 _ Ξ£aβ»ΒΉ

    Β·πInvR-Pos : isInvπ a
    Β·πInvR-Pos .fst = aβ»ΒΉ
    Β·πInvR-Pos .snd =
        sym (Β·π-Pos-helper a aβ»ΒΉ a>0 aβ»ΒΉ>0)
      β (Ξ» i β (path-πβ (absπ a) aβ (absβ₯0 a (aβ .snd)) i
          Β·πβ path-πβ (absπ aβ»ΒΉ) aββ»ΒΉ (absβ₯0 aβ»ΒΉ (aββ»ΒΉ .snd)) i) .fst)
      β Ξ£aβ»ΒΉ .snd


  Β·πInvR-Neg : (a : π)(a<0 : a <π π) β isInvπ a
  Β·πInvR-Neg a a<0 = -π -aβ»ΒΉ , Β·π-neg a -aβ»ΒΉ β sym (neg-Β·π a -aβ»ΒΉ) β  Ξ£-aβ»ΒΉ .snd
    where Ξ£-aβ»ΒΉ : isInvπ (-π a)
          Ξ£-aβ»ΒΉ = Β·πInvR-Pos (-π a) (-reverse<0 a a<0)
          -aβ»ΒΉ : π
          -aβ»ΒΉ = Ξ£-aβ»ΒΉ .fst


  Β·πInvR : (a : π) β Β¬ a β‘ π β isInvπ a
  Β·πInvR a Β¬aβ‘0 = case-split (trichotomyπ a π)
    where
    case-split : Trichotomyπ a π β isInvπ a
    case-split (gt a>0) = Β·πInvR-Pos a a>0
    case-split (lt a<0) = Β·πInvR-Neg a a<0
    case-split (eq aβ‘0) = Empty.rec (Β¬aβ‘0 aβ‘0)


  {-

    Ordered Field Instance

  -}

  isFieldπ : isField πCommRing
  isFieldπ = Β·πInvR

  πOrderedField : OrderedField (β-max β β') (β-max β β')
  πOrderedField = πOrderedRing , isFieldπ
