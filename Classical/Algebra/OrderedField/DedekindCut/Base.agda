{-

The Dedekind Cut

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.DedekindCut.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection

open import Classical.Axioms
open import Classical.Foundations.Powerset
open import Classical.Algebra.OrderedField

private
  variable
    β β' : Level


private
  module Helpers {β : Level}(π‘ : CommRing β) where
    open CommRingStr (π‘ .snd)

    helper1 : (a b c d : π‘ .fst) β c + ((a + b) - d) β‘ a + (b + (c - d))
    helper1 = solve π‘

    helper2 : (c d : π‘ .fst) β c β‘ c + (d - d)
    helper2 = solve π‘

    helper1' : (a b c d : π‘ .fst) β c Β· ((a Β· b) Β· d) β‘ a Β· (b Β· (c Β· d))
    helper1' = solve π‘


module Basics β¦ π€ : Oracle β¦
  (π¦ : OrderedField β β')
  where

  open Oracle π€

  private
    K = π¦ .fst .fst .fst


  open OrderedFieldStr π¦

  open Helpers (π¦ .fst .fst)


  {-

    Dedekind Cut

  -}

  record DedekindCut : Type (β-max β β') where
    no-eta-equality

    field

      upper : β K
      upper-inhab : β₯ Ξ£[ q β K ] q β upper β₯β
      upper-close : (r : K)(q : K) β q β upper β q < r β r β upper
      upper-round : (q : K) β q β upper β β₯ Ξ£[ r β K ] (r < q) Γ (r β upper) β₯β
      lower-inhab : β₯ Ξ£[ q β K ] ((r : K) β r β upper β q < r) β₯β


  open DedekindCut


  -- Dedekind Completion of K

  π : Type (β-max β β')
  π = DedekindCut


  {-

    hLevel of π

  -}

  -- Construct path in π from path of two cuts

  path-π : (a b : DedekindCut) β a .upper β‘ b .upper β a β‘ b
  path-π a b upper-path i .upper = upper-path i
  path-π a b upper-path i .upper-inhab =
    isPropβPathP (Ξ» i β squashβ {A = Ξ£[ q β K ] q β upper-path i}) (a .upper-inhab) (b .upper-inhab) i
  path-π a b upper-path i .upper-close =
    isPropβPathP (Ξ» i β isPropΞ 4 {C = Ξ» _ q β q β upper-path i} (Ξ» _ _ _ _ β isPropβ (upper-path i)))
    (a .upper-close) (b .upper-close) i
  path-π a b upper-path i .upper-round =
    isPropβPathP (Ξ» i β isPropΞ 2 {B = Ξ» q β q β upper-path i}
      (Ξ» q _ β squashβ {A = Ξ£[ r β K ] (r < q) Γ (r β upper-path i)}))
    (a .upper-round) (b .upper-round) i
  path-π a b upper-path i .lower-inhab =
    isPropβPathP (Ξ» i β squashβ {A = Ξ£[ q β K ] ((r : K) β r β upper-path i β q < r)})
    (a .lower-inhab) (b .lower-inhab) i

  -- π is hSet

  isSetπ : isSet π
  isSetπ a b p q i j =
    hcomp (Ξ» k β Ξ»
      { (i = i0) β path-π (lift-square i0 j) (p j) refl k
      ; (i = i1) β path-π (lift-square i1 j) (q j) refl k
      ; (j = i0) β path-π a a refl k
      ; (j = i1) β path-π b b refl k })
    (lift-square i j)
    where
    lift-square : (i j : I) β π
    lift-square i j = path-π a b
      (isSetβSquareP (Ξ» _ _ β isSetβ {X = K}) (cong upper p) (cong upper q) refl refl i) j


  {-

    Inclusion of K into π

  -}

  -- Rational number is real number

  _<P_ : K β K β hProp β'
  _<P_ p q = (p < q) , isProp<

  Kβπ : K β π
  Kβπ q .upper = specify (q <P_)
  Kβπ q .upper-inhab = β£ q + 1r , Inhabββ (q <P_) q+1>q β£β
  Kβπ q .upper-close r s sβupper r>s = Inhabββ (q <P_) (<-trans (ββInhab (q <P_) sβupper) r>s)
  Kβπ q .upper-round r rβupper = β£ middle q r , middle<r {p = q} {q = r} r>q , Inhabββ (q <P_) (middle>l r>q) β£β
    where r>q : r > q
          r>q = ββInhab (q <P_) rβupper
  Kβπ q .lower-inhab = β£ q - 1r , (Ξ» r rβupper β <-trans q-1<q (ββInhab (q <P_) rβupper)) β£β


  -- Zero and Unit

  π : π
  π = Kβπ 0r

  π : π
  π = Kβπ 1r


  {-

    The natural order on π

  -}

  _β€π_ : π β π β Type β
  a β€π b = b .upper β a .upper

  _β₯π_ : π β π β Type β
  a β₯π b = b β€π a

  isPropβ€π : {a b : π} β isProp (a β€π b)
  isPropβ€π = isPropβ

  β€π-refl : {a b : π} β a β‘ b β a β€π b
  β€π-refl aβ‘b {x = q} qβupper = subst (Ξ» p β q β p .upper) (sym aβ‘b) qβupper

  β€π-asym : {a b : π} β a β€π b β b β€π a β a β‘ b
  β€π-asym aβ€b bβ€a = path-π _ _ (biβββ‘ bβ€a aβ€b)


  {-

    Non-membership of upper cut

  -}

  module _ (a : π)(q : K) where

    Β¬βupperβ<upper : Β¬ q β a .upper β (r : K) β r β a .upper β q < r
    Β¬βupperβ<upper Β¬qβupper r rβupper = case-split (trichotomy q r)
      where
      case-split : Trichotomy q r β q < r
      case-split (lt q<r) = q<r
      case-split (eq qβ‘r) = Empty.rec (Β¬qβupper (subst (_β a .upper) (sym qβ‘r) rβupper))
      case-split (gt q>r) = Empty.rec (Β¬qβupper (a .upper-close _ _ rβupper q>r))

    <upperβΒ¬βupper : ((r : K) β r β a .upper β q < r) β Β¬ q β a .upper
    <upperβΒ¬βupper q<rβupper = case-split (decide (isPropβ (a .upper)))
      where
      case-split : Dec (q β a .upper) β Β¬ q β a .upper
      case-split (yes p) _ = <-arefl (q<rβupper q p) refl
      case-split (no Β¬p) = Β¬p


  Β¬βupper-close : (a : π)(p q : K) β Β¬ q β a .upper β p < q β Β¬ p β a .upper
  Β¬βupper-close a p q Β¬qβupper p<q =
    <upperβΒ¬βupper a _ (Ξ» r rβupper β <-trans p<q (Β¬βupperβ<upper a _ Β¬qβupper r rβupper))


  {-

    Basic algebraic operations of π

  -}


  -- Additive Inverse

  -upper : (a : π)(x : K) β hProp (β-max β β')
  -upper a x = β₯ Ξ£[ p β K ] ((r : K) β r β a .upper β p < r) Γ (x > - p) β₯β , squashβ

  -π_ : π β π
  (-π a) .upper = specify (-upper a)
  (-π a) .upper-inhab = Prop.map
    (Ξ» (q , q<rβupper) β
      (- q) + 1r , Inhabββ (-upper a) β£ q , q<rβupper , q+1>q β£β )
    (a .lower-inhab)
  (-π a) .upper-close r q qβupper q<r = Prop.rec (isPropβ ((-π a) .upper))
    (Ξ» (p , p<rβupper , q>-p) β
      Inhabββ (-upper a) β£ p , p<rβupper , <-trans q>-p q<r β£β)
    (ββInhab (-upper a) qβupper)
  (-π a) .upper-round q qβupper = Prop.map
    (Ξ» (p , p<rβupper , q>-p) β
      middle (- p) q , middle<r q>-p  , Inhabββ (-upper a) β£ p , p<rβupper , middle>l q>-p β£β)
    (ββInhab (-upper a) qβupper)
  (-π a) .lower-inhab = Prop.map
    (Ξ» (q , qβupper) β
      - q , Ξ» r rβupper β Prop.rec isProp<
        (Ξ» (p , p<sβupper , r>-p) β
          <-trans (-Reverse< (p<sβupper q qβupper)) r>-p)
        (ββInhab (-upper a) rβupper))
    (a .upper-inhab)


  -- Addition

  +upper : π β π β K β hProp β
  +upper a b r = β₯ Ξ£[ p β K ] Ξ£[ q β K ] p β a .upper Γ q β b .upper Γ (r β‘ p + q) β₯β , squashβ

  private
    alg-helper : (a b c d : K) β d β‘ a + b β c β‘ a + (b + (c - d))
    alg-helper a b c d dβ‘a+b = helper2 c d β (Ξ» i β c + (dβ‘a+b i - d)) β helper1 a b c d

  _+π_ : π β π β π
  (a +π b) .upper = specify (+upper a b)
  (a +π b) .upper-inhab = Prop.map2
    (Ξ» (p , pβupper) (q , qβupper) β
      p + q , Inhabββ (+upper a b) β£ p , q , pβupper , qβupper , refl β£β)
    (a .upper-inhab) (b .upper-inhab)
  (a +π b) .upper-close r q qβupper q<r = Prop.rec (isPropβ ((a +π b) .upper))
    (Ξ» (s , t , sβupper , tβupper , qβ‘s+t) β
      let t+r-qβupper : (t + (r - q)) β b .upper
          t+r-qβupper = b .upper-close _ _ tβupper (+-rPosβ> (>βDiff>0 q<r))
          rβ‘s+t+r-q : r β‘ s + (t + (r - q))
          rβ‘s+t+r-q = alg-helper s t r q qβ‘s+t
      in  Inhabββ (+upper a b) β£ s , t + (r - q) , sβupper , t+r-qβupper , rβ‘s+t+r-q β£β)
    (ββInhab (+upper a b) qβupper)
  (a +π b) .upper-round q qβupper = Prop.rec squashβ
    (Ξ» (s , t , sβupper , tβupper , qβ‘s+t) β Prop.map2
      (Ξ» (s' , s'<s , s'βupper) (t' , t'<t , t'βupper) β
        s' + t' , subst (s' + t' <_) (sym qβ‘s+t) (+-Pres< s'<s t'<t) ,
        Inhabββ (+upper a b) β£ s' , t' , s'βupper , t'βupper , refl β£β)
      (a .upper-round s sβupper) (b .upper-round t tβupper))
    (ββInhab (+upper a b) qβupper)
  (a +π b) .lower-inhab = Prop.map2
    (Ξ» (p , p<rβupper) (q , q<rβupper) β
        p + q , Ξ» r rβupper β Prop.rec isProp<
          (Ξ» (s , t , sβupper , tβupper , rβ‘s+t) β
            subst (p + q <_) (sym rβ‘s+t)
            (+-Pres< (p<rβupper s sβupper) (q<rβupper t tβupper)))
          (ββInhab (+upper a b) rβupper))
    (a .lower-inhab) (b .lower-inhab)


  {-

    Non-Negative Reals

  -}

  πβ : Type (β-max β β')
  πβ = Ξ£[ r β π ] (r β₯π π)

  path-πβ : (a b : πβ) β a .fst β‘ b .fst β a β‘ b
  path-πβ a b p i .fst = p i
  path-πβ a b p i .snd = isPropβPathP (Ξ» i β isPropβ€π {a = π} {b = p i}) (a .snd) (b .snd) i

  qβπββq>0 : (a : πβ)(q : K) β q β a .fst .upper β q > 0r
  qβπββq>0 a q qβupper = ββInhab (0r <P_) (a .snd qβupper)


  -- Zero and Unit

  πβ : πβ
  πβ = π , β‘ββ {A = π .upper} refl

  πβ : πβ
  πβ = π , Ξ» qβupper β Inhabββ (0r <P_) (<-trans 1>0 (ββInhab (1r <P_) qβupper))


  -- Addition

  +upperβ : πβ β πβ β K β hProp β
  +upperβ a b = +upper (a .fst) (b .fst)

  _+πβ_ : (a b : πβ) β πβ
  ((a , aβ₯0) +πβ (b , bβ₯0)) .fst = a +π b
  ((a , aβ₯0) +πβ (b , bβ₯0)) .snd qβupper =
    Prop.rec (isPropβ (π .upper))
    (Ξ» (s , t , sβupper , tβupper , qβ‘s+t) β
      let s>0 = ββInhab (0r <P_) (aβ₯0 sβupper)
          t>0 = ββInhab (0r <P_) (bβ₯0 tβupper)
      in  Inhabββ (0r <P_) (subst (_> 0r) (sym qβ‘s+t) (+-Pres>0 s>0 t>0)))
    (ββInhab (+upper a b) qβupper)


  -- Multiplication

  Β·upper : π β π β K β hProp β
  Β·upper a b r = β₯ Ξ£[ p β K ] Ξ£[ q β K ] p β a .upper Γ q β b .upper Γ (r β‘ p Β· q) β₯β , squashβ

  Β·upperβ : πβ β πβ β K β hProp β
  Β·upperβ a b = Β·upper (a .fst) (b .fst)


  β₯π0+qβupperβq>0 : (a : π){q : K} β a β₯π π β q β a .upper β q > 0r
  β₯π0+qβupperβq>0 a {q = q} aβ₯0 qβupper = ββInhab (0r <P_) (aβ₯0 qβupper)

  qβΒ·upperβq>0 : (a b : π) β a β₯π π β b β₯π π β (q : K) β q β specify (Β·upper a b) β q > 0r
  qβΒ·upperβq>0 a b aβ₯0 bβ₯0 q qβupper = Prop.rec isProp<
    (Ξ» (s , t , sβupper , tβupper , qβ‘sΒ·t) β
      subst (_> 0r) (sym qβ‘sΒ·t)
        (Β·-Pres>0 (β₯π0+qβupperβq>0 a aβ₯0 sβupper) (β₯π0+qβupperβq>0 b bβ₯0 tβupper)))
    (ββInhab (Β·upper a b) qβupper)

  private
    alg-helper' : (a b c d : K)(dβ’0 : Β¬ d β‘ 0r) β d β‘ a Β· b β c β‘ a Β· (b Β· (c Β· inv dβ’0))
    alg-helper' a b c d dβ’0 dβ‘aΒ·b =
        sym (Β·IdR c) β (Ξ» i β c Β· Β·-rInv dβ’0 (~ i))
      β (Ξ» i β c Β· (dβ‘aΒ·b i Β· inv dβ’0)) β helper1' a b c (inv dβ’0)

  _Β·πβ_ : (a b : πβ) β πβ
  ((a , aβ₯0) Β·πβ (b , bβ₯0)) .fst .upper = specify (Β·upper a b)
  ((a , aβ₯0) Β·πβ (b , bβ₯0)) .fst .upper-inhab = Prop.map2
    (Ξ» (p , pβupper) (q , qβupper) β
      p Β· q , Inhabββ (Β·upper a b) β£ p , q , pβupper , qβupper , refl β£β)
    (a .upper-inhab) (b .upper-inhab)
  ((a , aβ₯0) Β·πβ (b , bβ₯0)) .fst .upper-close r q qβupper q<r =
    Prop.rec (isPropβ (((a , aβ₯0) Β·πβ (b , bβ₯0)) .fst .upper))
    (Ξ» (s , t , sβupper , tβupper , qβ‘sΒ·t) β
      let q>0 : q > 0r
          q>0 = qβΒ·upperβq>0 a b aβ₯0 bβ₯0 q qβupper
          qβ’0 : Β¬ q β‘ 0r
          qβ’0 = >-arefl q>0
          qβ»ΒΉ = inv qβ’0
          tΒ·rΒ·qβ»ΒΉβupper : (t Β· (r Β· qβ»ΒΉ)) β b .upper
          tΒ·rΒ·qβ»ΒΉβupper = b .upper-close _ _ tβupper
            (Β·-PosΒ·>1β> (β₯π0+qβupperβq>0 b bβ₯0 tβupper) (p>q>0βpΒ·qβ»ΒΉ>1 q>0 q<r))
          rβ‘sΒ·tΒ·rΒ·qβ»ΒΉ : r β‘ s Β· (t Β· (r Β· qβ»ΒΉ))
          rβ‘sΒ·tΒ·rΒ·qβ»ΒΉ = alg-helper' s t r q qβ’0 qβ‘sΒ·t
      in  Inhabββ (Β·upper a b) β£ s , t Β· (r Β· qβ»ΒΉ) , sβupper , tΒ·rΒ·qβ»ΒΉβupper , rβ‘sΒ·tΒ·rΒ·qβ»ΒΉ β£β)
    (ββInhab (Β·upper a b) qβupper)
  ((a , aβ₯0) Β·πβ (b , bβ₯0)) .fst .upper-round q qβupper = Prop.rec squashβ
    (Ξ» (s , t , sβupper , tβupper , qβ‘sΒ·t) β Prop.map2
      (Ξ» (s' , s'<s , s'βupper) (t' , t'<t , t'βupper) β
        s' Β· t' , subst (s' Β· t' <_) (sym qβ‘sΒ·t)
          (Β·-PosPres> (β₯π0+qβupperβq>0 a aβ₯0 s'βupper) (β₯π0+qβupperβq>0 b bβ₯0 t'βupper) s'<s t'<t) ,
        Inhabββ (Β·upper a b) β£ s' , t' , s'βupper , t'βupper , refl β£β )
      (a .upper-round s sβupper) (b .upper-round t tβupper))
    (ββInhab (Β·upper a b) qβupper)
  ((a , aβ₯0) Β·πβ (b , bβ₯0)) .fst .lower-inhab =
    β£ - 1r , (Ξ» r rβupper β <-trans -1<0 (qβΒ·upperβq>0 a b aβ₯0 bβ₯0 r rβupper)) β£β
  ((a , aβ₯0) Β·πβ (b , bβ₯0)) .snd qβupper =
    Prop.rec (isPropβ (π .upper))
    (Ξ» (s , t , sβupper , tβupper , qβ‘sΒ·t) β
      let s>0 = ββInhab (0r <P_) (aβ₯0 sβupper)
          t>0 = ββInhab (0r <P_) (bβ₯0 tβupper)
      in  Inhabββ (0r <P_) (subst (_> 0r) (sym qβ‘sΒ·t) (Β·-Pres>0 s>0 t>0)))
    (ββInhab (Β·upper a b) qβupper)


  -- Multiplicative Inverse

  inv-upper : (a : π)(x : K) β hProp (β-max β β')
  inv-upper a x = β₯ Ξ£[ p β K ] Ξ£[ p>0 β p > 0r ] ((r : K) β r β a .upper β p < r) Γ (x > inv (>-arefl p>0)) β₯β , squashβ

  invπβ : (a : π)(q : K) β q > 0r β ((r : K) β r β a .upper β q < r) β πβ
  invπβ a _ _ _ .fst .upper = specify (inv-upper a)
  invπβ a qβ qβ>0 qβ<rβupper .fst .upper-inhab =
    let qββ»ΒΉ = inv (>-arefl qβ>0) in
    β£ qββ»ΒΉ + 1r , Inhabββ (inv-upper a) β£ qβ , qβ>0 , qβ<rβupper , q+1>q {q = qββ»ΒΉ} β£β β£β
  invπβ a qβ qβ>0 qβ<rβupper .fst .upper-close r q qβupper q<r =
    Prop.rec (isPropβ (invπβ a qβ qβ>0 qβ<rβupper .fst .upper))
    (Ξ» (p , p>0 , p<rβupper , q>pβ»ΒΉ) β
      Inhabββ (inv-upper a) β£ p , p>0 , p<rβupper , <-trans q>pβ»ΒΉ q<r β£β)
    (ββInhab (inv-upper a) qβupper)
  invπβ a _ _ _ .fst .upper-round q qβupper = Prop.map
    (Ξ» (p , p>0 , p<rβupper , q>pβ»ΒΉ) β
      let pβ»ΒΉ = inv (>-arefl p>0) in
      middle pβ»ΒΉ q , middle<r q>pβ»ΒΉ  , Inhabββ (inv-upper a) β£ p , p>0 , p<rβupper , middle>l q>pβ»ΒΉ β£β)
    (ββInhab (inv-upper a) qβupper)
  invπβ a qβ qβ>0 qβ<rβupper .fst .lower-inhab = Prop.map
    (Ξ» (q , qβupper) β
      let q>0 = <-trans qβ>0 (qβ<rβupper q qβupper)
          qβ»ΒΉ = inv (>-arefl q>0) in
      qβ»ΒΉ , Ξ» r rβupper β Prop.rec isProp<
        (Ξ» (p , p>0 , p<sβupper , r>pβ»ΒΉ) β
          <-trans (inv-Reverse< _ _ (p<sβupper q qβupper)) r>pβ»ΒΉ)
        (ββInhab (inv-upper a) rβupper))
    (a .upper-inhab)
  invπβ a _ _ _ .snd qβupper =
    Prop.rec (isPropβ (π .upper))
    (Ξ» (p , p>0 , p<rβupper , q>pβ»ΒΉ) β
      Inhabββ (0r <P_) (<-trans (p>0βpβ»ΒΉ>0 p>0) q>pβ»ΒΉ))
    (ββInhab (inv-upper a) qβupper)
