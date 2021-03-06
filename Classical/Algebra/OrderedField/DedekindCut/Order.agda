{-

Order Structure on Dedekind Cuts

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Algebra.OrderedField.DedekindCut.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Preliminary.Logic
open import Classical.Axioms
open import Classical.Foundations.Powerset

open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.DedekindCut.Base
open import Classical.Algebra.OrderedField.DedekindCut.Algebra
open import Classical.Algebra.OrderedField.DedekindCut.Signature

private
  variable
    β β' : Level


module Order β¦ π€ : Oracle β¦
  (π¦ : OrderedField β β')(archimedes : isArchimedean (π¦ . fst))
  where

  open Oracle π€

  private
    K = π¦ .fst .fst .fst

  open OrderedFieldStr π¦
  open Basics   π¦
  open Algebra  π¦ archimedes
  open DedekindCut

  {-

    Strict Ordering

  -}

  _<π_ : π β π β Type (β-max β β')
  a <π b = β₯ Ξ£[ q β K ] ((r : K) β r β b .upper β q < r) Γ q β a .upper β₯β

  _>π_ : π β π β Type (β-max β β')
  a >π b = b <π a

  isProp<π : {a b : π} β isProp (a <π b)
  isProp<π = squashβ


  Kβπ-Pres> : (x y : K) β x < y β (Kβπ x) <π (Kβπ y)
  Kβπ-Pres> x y x<y = β£ middle x y ,
    (Ξ» q qβy β <-trans (middle<r x<y) (ββInhab (y <P_) qβy)) ,
    Inhabββ (x <P_) (middle>l x<y) β£β

  1>π0 : π >π π
  1>π0 = Kβπ-Pres> 0r 1r 1>0


  -- Strictness

  <πββ€π : {a b : π} β a <π b β a β€π b
  <πββ€π {a = a} a<b xβupper = Prop.rec (isPropβ (a .upper))
    (Ξ» (q , q<rβupper , qβupper) β a .upper-close _ _ qβupper (q<rβupper _ xβupper)) a<b

  <π-arefl : {a b : π} β a <π b β a β‘ b β β₯
  <π-arefl {a = a} {b = b} a<b aβ‘b = Prop.rec isPropβ₯
    (Ξ» (q , q<rβupper , qβupper) β
      <upperβΒ¬βupper b _ q<rβupper (subst (Ξ» x β q β x .upper) aβ‘b qβupper)) a<b

  >π-arefl : {a b : π} β b <π a β a β‘ b β β₯
  >π-arefl h p = <π-arefl h (sym p)


  <β€π-asym : (a b : π) β a <π b β a β₯π b β β₯
  <β€π-asym a b a<b aβ₯b = <π-arefl {a = a} {b = b} a<b (β€π-asym (<πββ€π {a = a} {b = b} a<b) aβ₯b)

  <π-asym : (a b : π) β a <π b β a >π b β β₯
  <π-asym a b a<b b<a = <β€π-asym a b a<b (<πββ€π {a = b} {b = a} b<a)


  -- Tons of properties

  Β¬aβ€bβa>b : (a b : π) β Β¬ (a β€π b) β a >π b
  Β¬aβ€bβa>b a b Β¬aβ€b = Prop.map
    (Ξ» (x , Β¬xβupper , xβupper) β x , Β¬βupperβ<upper a x Β¬xβupper , xβupper)
    (βββ Β¬aβ€b)

  Β¬a>bβaβ€b : (a b : π) β Β¬ (a >π b) β a β€π b
  Β¬a>bβaβ€b a b Β¬a>b = Β¬Β¬elim (isPropβ€π {a = a} {b = b}) (Β¬map (Β¬aβ€bβa>b a b) Β¬a>b)

  aβ€bβa<b+aβ‘b : (a b : π) β a β€π b β (a <π b) β (a β‘ b)
  aβ€bβa<b+aβ‘b a b aβ€b with decide (isProp<π {a = a} {b = b})
  ... | yes a<b = inl a<b
  ... | no Β¬a<b = inr (β€π-asym aβ€b (Β¬a>bβaβ€b b a Β¬a<b))


  data Trichotomyπ (a b : π) : Type (β-max β β') where
    gt : a >π b β Trichotomyπ a b
    eq : a β‘ b  β Trichotomyπ a b
    lt : a <π b β Trichotomyπ a b

  trichotomyπ : (a b : π) β Trichotomyπ a b
  trichotomyπ a b with decide (isProp<π {a = a} {b = b})
  ... | yes a<b = lt a<b
  ... | no Β¬a<b =
    case aβ€bβa<b+aβ‘b b a (Β¬a>bβaβ€b b a Β¬a<b) of Ξ»
    { (inl b<a) β gt b<a
    ; (inr bβ‘a) β eq (sym bβ‘a) }


  data Dichotomyπ (a b : π) : Type (β-max β β') where
    ge : a β₯π b β Dichotomyπ a b
    lt : a <π b β Dichotomyπ a b

  dichotomyπ : (a b : π) β Dichotomyπ a b
  dichotomyπ a b with decide (isProp<π {a = a} {b = b})
  ... | yes a<b = lt a<b
  ... | no Β¬a<b = ge (Β¬a>bβaβ€b b a Β¬a<b)


  data Splitβ€π (a b : π)(aβ€b : a β€π b) : Type (β-max β β') where
    lt : a <π b β Splitβ€π a b aβ€b
    eq : a β‘ b  β Splitβ€π a b aβ€b

  splitβ€π : (a b : π) β (aβ€b : a β€π b) β Splitβ€π a b aβ€b
  splitβ€π a b aβ€b with dichotomyπ a b
  ... | lt a<b = lt a<b
  ... | ge aβ₯b = eq (β€π-asym aβ€b aβ₯b)


  +π-Pres< : (a b c d : π) β a <π b β c <π d β (a +π c) <π (b +π d)
  +π-Pres< a b c d a<b b<c = Prop.map2
    (Ξ» (q , q<bβupper , qβaupper) (p , p<dβupper , pβcupper) β
      q + p ,
      (Ξ» x xβb+d β Prop.rec isProp<
        (Ξ» (s , t , sβb , tβd , xβ‘s+t) β
          subst (q + p <_) (sym xβ‘s+t) (+-Pres< (q<bβupper s sβb) (p<dβupper t tβd)))
        (ββInhab (+upper b d) xβb+d)) ,
      Inhabββ (+upper a c) β£ q , p , qβaupper , pβcupper , refl β£β )
    a<b b<c

  +π-Presβ€ : (a b c d : π) β a β€π b β c β€π d β (a +π c) β€π (b +π d)
  +π-Presβ€ a b c d aβ€b cβ€d xβb+d =
    Prop.rec (isPropβ ((a +π c) .upper))
    (Ξ» (s , t , sβb , tβd , xβ‘s+t) β
      Inhabββ (+upper a c) β£ s , t , aβ€b sβb , cβ€d tβd , xβ‘s+t β£β)
    (ββInhab (+upper b d) xβb+d)

  +π-rPresβ€ : (a b c : π) β a β€π b β (a +π c) β€π (b +π c)
  +π-rPresβ€ a b c aβ€b = +π-Presβ€ a b c c aβ€b (β€π-refl {a = c} refl)

  private
    alg-helper'' : (a c : π) β (a +π c) +π (-π c) β‘ a
    alg-helper'' a c = sym (+πAssoc _ _ _) β (Ξ» i β a +π +πInvR c i) β +πIdR a

    alg-helper''' : (a b c : π) β (a +π b) +π c β‘ (a +π c) +π b
    alg-helper''' a b c = sym (+πAssoc _ _ _) β (Ξ» i β a +π +πComm b c i) β +πAssoc _ _ _

  +π-rPresβ€- : (a b c : π) β (a +π c) β€π (b +π c) β a β€π b
  +π-rPresβ€- a b c a+cβ€b+c = transport (Ξ» i β alg-helper'' a c i β€π alg-helper'' b c i)
    (+π-rPresβ€ (a +π c) (b +π c) (-π c) a+cβ€b+c)

  +π-rPres< : (a b c : π) β a <π b β (a +π c) <π (b +π c)
  +π-rPres< a b c a<b = Β¬aβ€bβa>b (b +π c) (a +π c) (Β¬map (+π-rPresβ€- b a c) (<β€π-asym a b a<b))


  <π-reverse' : (a b : π) β a <π b β (-π b) <π (-π a)
  <π-reverse' a b a<b = transport (Ξ» i β path1 i <π path2 i)
    (+π-rPres< (a +π (-π a)) (b +π (-π a)) (-π b) (+π-rPres< a b (-π a) a<b))
    where
    path1 : (a +π (-π a)) +π (-π b) β‘ (-π b)
    path1 = (Ξ» i β +πInvR a i +π (-π b)) β +πIdL (-π b)
    path2 : (b +π (-π a)) +π (-π b) β‘ (-π a)
    path2 = alg-helper''' _ _ _ β (Ξ» i β +πInvR b i +π (-π a)) β +πIdL (-π a)

  <π-reverse : (a b : π) β a <π b β (-π b) β€π (-π a)
  <π-reverse a b a<b = <πββ€π {a = (-π b)} {b = (-π a)} (<π-reverse' a b a<b)

  -0β‘0 : -π π β‘ π
  -0β‘0 = sym (+πIdR (-π π)) β +πInvL π

  -reverse>0 : (a : π) β a >π π β (-π a) <π π
  -reverse>0 a a>0 = subst ((-π a) <π_) -0β‘0 (<π-reverse' π a a>0)

  -reverse<0 : (a : π) β a <π π β (-π a) >π π
  -reverse<0 a a<0 = subst (_<π (-π a)) -0β‘0 (<π-reverse' a π a<0)

  <0-reverse : (a : π) β a <π π β (-π a) β₯π π
  <0-reverse a a<0 = <πββ€π {a = π} {b = (-π a)} (-reverse<0 a a<0)


  +π-Pres<0 : (a b : π) β a <π π β b <π π β (a +π b) <π π
  +π-Pres<0 a b a<0 b<0 = subst ((a +π b) <π_) (+πIdR π) (+π-Pres< a π b π a<0 b<0)

  +π-Presβ₯0 : (a b : π) β a β₯π π β b β₯π π β (a +π b) β₯π π
  +π-Presβ₯0 a b aβ₯0 bβ₯0 = subst ((a +π b) β₯π_) (+πIdR π) (+π-Presβ€ π a π b aβ₯0 bβ₯0)

  +π-Pres>0 : (a b : π) β a >π π β b >π π β (a +π b) >π π
  +π-Pres>0 a b a>0 b>0 = subst ((a +π b) >π_) (+πIdR π) (+π-Pres< π a π b a>0 b>0)


  Β·π-Pres>0 : (a b : πβ) β a .fst >π π β b .fst >π π β (a Β·πβ b) .fst >π π
  Β·π-Pres>0 a b a>0 b>0 = Prop.map2
    (Ξ» (q , q<rβa , qβπ) (p , p<rβb , pβπ) β
      let q>0 = qβπββq>0 πβ q qβπ
          p>0 = qβπββq>0 πβ p pβπ in
      q Β· p ,
      (Ξ» x xβaΒ·b β Prop.rec isProp<
        (Ξ» (s , t , sβa , tβb , xβ‘sΒ·t) β
          subst (q Β· p <_) (sym xβ‘sΒ·t)
            (Β·-PosPres> q>0 p>0 (q<rβa s sβa) (p<rβb t tβb)))
        (ββInhab (Β·upperβ a b) xβaΒ·b)) ,
      Inhabββ (0r <P_) (Β·-Pres>0 q>0 p>0) )
    a>0 b>0


  -- Two lemmas for convenient case-splitting

  aβ₯0+-aβ₯0βaβ‘0 : {a : π} β a β₯π π β (-π a) β₯π π β a β‘ π
  aβ₯0+-aβ₯0βaβ‘0 {a = a} aβ₯0 -aβ₯0 with splitβ€π π a aβ₯0
  ... | lt 0<a = Empty.rec (<β€π-asym (-π a) π (-reverse>0 a 0<a) -aβ₯0)
  ... | eq 0β‘a = sym 0β‘a

  a<0+-a<0ββ₯ : {a : π} β a <π π β (-π a) <π π β β₯
  a<0+-a<0ββ₯ {a = a} a<0 -a<0 = <π-asym (-π a) π -a<0 (-reverse<0 a a<0)

  a>0+-a>0ββ₯ : {a : π} β a >π π β (-π a) >π π β β₯
  a>0+-a>0ββ₯ {a = a} a>0 -a>0 = <π-asym π (-π a) -a>0 (-reverse>0 a a>0)


  {-

    Absolute Value

  -}

  absπ : π β πβ
  absπ a with trichotomyπ a π
  ... | gt a>0 = a , <πββ€π {a = π} {b = a} a>0
  ... | eq aβ‘0 = πβ
  ... | lt a<0 = -π a , subst (_β€π (-π a)) -0β‘0 (<π-reverse a π a<0)

  abs-π : (a : π) β absπ (-π a) β‘ absπ a
  abs-π a with trichotomyπ a π | trichotomyπ (-π a) π
  ... | gt a>0 | gt -a>0 = Empty.rec (a>0+-a>0ββ₯ {a = a} a>0 -a>0)
  ... | lt a<0 | lt -a<0 = Empty.rec (a<0+-a<0ββ₯ {a = a} a<0 -a<0)
  ... | eq aβ‘0 | gt -a>0 = path-πβ _ _ -aβ‘0
    where -aβ‘0 : -π a β‘ π
          -aβ‘0 = (Ξ» i β -π (aβ‘0 i)) β -0β‘0
  ... | eq aβ‘0 | eq -aβ‘0 = refl
  ... | eq aβ‘0 | lt -a<0 = path-πβ _ _ -aβ‘0
    where -aβ‘0 : -π (-π a) β‘ π
          -aβ‘0 = (Ξ» i β -π (-π (aβ‘0 i))) β -πInvolutive π
  ... | gt a>0 | eq -aβ‘0 = path-πβ _ _ (sym aβ‘0)
    where aβ‘0 : a β‘ π
          aβ‘0 = sym (-πInvolutive a) β (Ξ» i β -π (-aβ‘0 i)) β -0β‘0
  ... | lt a<0 | eq -aβ‘0 = path-πβ _ _ (sym -aβ‘0)
  ... | gt a>0 | lt -a<0 = path-πβ _ _ (-πInvolutive a)
  ... | lt a<0 | gt -a>0 = path-πβ _ _ refl


  {-

    Signature

  -}

  sign : π β Sign
  sign a with trichotomyπ a π
  ... | gt a>0 = pos
  ... | eq aβ‘0 = nul
  ... | lt a<0 = neg

  signed : Sign β πβ β π
  signed pos a = a .fst
  signed nul a = π
  signed neg a = -π a .fst


  sign>0 : (a : π) β a >π π β sign a β‘ pos
  sign>0 a a>0 with trichotomyπ a π
  ... | gt a>0 = refl
  ... | eq aβ‘0 = Empty.rec (<π-arefl a>0 (sym aβ‘0))
  ... | lt a<0 = Empty.rec (<π-asym π a a>0 a<0)

  signβ‘0 : (a : π) β a β‘ π β sign a β‘ nul
  signβ‘0 a aβ‘0 with trichotomyπ a π
  ... | gt a>0 = Empty.rec (<π-arefl a>0 (sym aβ‘0))
  ... | eq aβ‘0 = refl
  ... | lt a<0 = Empty.rec (<π-arefl a<0 aβ‘0)

  sign<0 : (a : π) β a <π π β sign a β‘ neg
  sign<0 a a<0 with trichotomyπ a π
  ... | gt a>0 = Empty.rec (<π-asym π a a>0 a<0)
  ... | eq aβ‘0 = Empty.rec (<π-arefl a<0 aβ‘0)
  ... | lt a<0 = refl

  signβ₯0 : (a : π) β a β₯π π β sign a β₯0s
  signβ₯0 a aβ₯0 with trichotomyπ a π
  ... | gt a>0 = _
  ... | eq aβ‘0 = _
  ... | lt a<0 = Empty.rec (<β€π-asym a π a<0 aβ₯0)

  signπ : sign π β‘ nul
  signπ = signβ‘0 _ refl

  signπ : sign π β‘ pos
  signπ = sign>0 π 1>π0


  -sign : (a : π) β sign (-π a) β‘ -s (sign a)
  -sign a with trichotomyπ a π
  ... | gt a>0 = sign<0 (-π a) (-reverse>0 a a>0)
  ... | eq aβ‘0 = signβ‘0 (-π a) ((Ξ» i β -π (aβ‘0 i)) β -0β‘0)
  ... | lt a<0 = sign>0 (-π a) (-reverse<0 a a<0)


  signedπ : (s : Sign) β signed s πβ β‘ π
  signedπ pos = refl
  signedπ nul = refl
  signedπ neg = -0β‘0

  signed- : (s : Sign)(a : πβ) β signed (-s s) a β‘ -π (signed s a)
  signed- pos a = refl
  signed- nul a = sym -0β‘0
  signed- neg a = sym (-πInvolutive _)


  abs>0 : (a : π) β a >π π β absπ a .fst >π π
  abs>0 a a>0 with trichotomyπ a π
  ... | gt a>0 = a>0
  ... | eq aβ‘0 = Empty.rec (<π-arefl a>0 (sym aβ‘0))
  ... | lt a<0 = Empty.rec (<π-asym a π a<0 a>0)

  abs<0 : (a : π) β a <π π β absπ a .fst >π π
  abs<0 a a<0 with trichotomyπ a π
  ... | gt a>0 = Empty.rec (<π-asym a π a<0 a>0)
  ... | eq aβ‘0 = Empty.rec (<π-arefl a<0 aβ‘0)
  ... | lt a<0 = -reverse<0 a a<0

  absβ₯0 : (a : π) β a β₯π π β absπ a .fst β‘ a
  absβ₯0 a aβ₯0 with trichotomyπ a π
  ... | gt a>0 = refl
  ... | eq aβ‘0 = sym aβ‘0
  ... | lt a<0 = Empty.rec (<β€π-asym a π a<0 aβ₯0)


  absπ : absπ π β‘ πβ
  absπ = path-πβ _ _ (absβ₯0 π (πβ .snd))

  absβ‘0 : (a : π) β a β‘ π β absπ a β‘ πβ
  absβ‘0 a aβ‘0 = cong absπ aβ‘0 β absπ

  absπ : absπ π β‘ πβ
  absπ = path-πβ _ _ (absβ₯0 π (πβ .snd))


  sign-abs-β‘ : (a : π) β signed (sign a) (absπ a) β‘ a
  sign-abs-β‘ a with trichotomyπ a π
  ... | gt a>0 = refl
  ... | eq aβ‘0 = sym aβ‘0
  ... | lt a<0 = -πInvolutive a


  abs-signed : (s : Sign)(a : πβ) β Β¬ s β‘ nul β absπ (signed s a) β‘ a
  abs-signed pos (a , aβ₯0) Β¬sβ‘nul with trichotomyπ a π
  ... | gt a>0 = path-πβ _ _ refl
  ... | eq aβ‘0 = path-πβ _ _ (sym aβ‘0)
  ... | lt a<0 = Empty.rec (<β€π-asym a π a<0 aβ₯0)
  abs-signed nul _ Β¬sβ‘nul = Empty.rec (Β¬sβ‘nul refl)
  abs-signed neg (a , aβ₯0) Β¬sβ‘nul with trichotomyπ a π
  ... | gt a>0 = path-πβ _ _ ((Ξ» i β abs-π a i .fst) β absβ₯0 a aβ₯0)
  ... | eq aβ‘0 = path-πβ _ _ ((Ξ» i β abs-π a i .fst) β absβ₯0 a aβ₯0)
  ... | lt a<0 = Empty.rec (<β€π-asym a π a<0 aβ₯0)

  sign-signed : (s : Sign)(a : πβ) β Β¬ a .fst β‘ π β sign (signed s a) β‘ s
  sign-signed pos (a , aβ₯0) Β¬aβ‘0 with trichotomyπ a π
  ... | gt a>0 = refl
  ... | eq aβ‘0 = Empty.rec (Β¬aβ‘0 aβ‘0)
  ... | lt a<0 = Empty.rec (<β€π-asym a π a<0 aβ₯0)
  sign-signed nul (a , aβ₯0) Β¬aβ‘0 with trichotomyπ a π
  ... | gt a>0 = signβ‘0 π refl
  ... | eq aβ‘0 = Empty.rec (Β¬aβ‘0 aβ‘0)
  ... | lt a<0 = Empty.rec (<β€π-asym a π a<0 aβ₯0)
  sign-signed neg (a , aβ₯0) Β¬aβ‘0 with trichotomyπ a π
  ... | gt a>0 = sign<0 (-π a) (-reverse>0 a a>0)
  ... | eq aβ‘0 = Empty.rec (Β¬aβ‘0 aβ‘0)
  ... | lt a<0 = Empty.rec (<β€π-asym a π a<0 aβ₯0)
