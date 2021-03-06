{-

A Technical Lemma about Archimedean-ness

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.DedekindCut.Archimedes where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (β ; zero ; suc)
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection

open import Classical.Axioms
open import Classical.Preliminary.Nat
open import Classical.Foundations.Powerset

open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.DedekindCut.Base

private
  variable
    β β' : Level

private
  module Helpers {β : Level}(π‘ : CommRing β) where
    open CommRingStr (π‘ .snd)

    helper1 : (p q : π‘ .fst) β p + (q - p) β‘ q
    helper1 = solve π‘

    helper2 : (r u Ξ΅ : π‘ .fst) β (r + Ξ΅) - u β‘ (r - u) + Ξ΅
    helper2 = solve π‘

    helper3 : (a b c : π‘ .fst) β (a - b) + (b - c) β‘ a - c
    helper3 = solve π‘

    helper4 : (b c : π‘ .fst) β c + (b - c) β‘ b
    helper4 = solve π‘


module Archimedes β¦ π€ : Oracle β¦
  (π¦ : OrderedField β β')(archimedesK : isArchimedean (π¦ . fst))
  where

  open Oracle π€

  private
    K = π¦ .fst .fst .fst


  open OrderedFieldStr π¦
  open Basics   π¦
  open DedekindCut

  open Helpers (π¦ .fst .fst)


  module _  (a : π)(Ξ΅ : K)(Ξ΅>0 : Ξ΅ > 0r) where

    module _
      (p : K)(Β¬pβupper : Β¬ p β a .upper)
      where

      private
        P : β β Type
        P n = (p + n β Ξ΅) β a .upper

        isPropP : (n : β) β isProp (P n)
        isPropP _ = isPropβ (a .upper)

        decP : (n : β) β Dec (P n)
        decP n = decide (isPropP n)

        Β¬P0 : Β¬ P zero
        Β¬P0 p0 = Β¬pβupper (subst (_β a .upper) ((Ξ» i β p + 0βqβ‘0 Ξ΅ i) β +IdR p) p0)

        βPn : β₯ Ξ£[ n β β ] P n β₯β
        βPn = Prop.map
          (Ξ» (q , qβupper) β
            let (n , nΒ·Ξ΅>q-p) = archimedesK (q - p) Ξ΅ Ξ΅>0
                p+nΒ·Ξ΅>q : p + n β Ξ΅ > q
                p+nΒ·Ξ΅>q = subst (p + n β Ξ΅ >_) (helper1 p q) (+-lPres< {z = p} nΒ·Ξ΅>q-p)
            in  n , a .upper-close _ _ qβupper p+nΒ·Ξ΅>q)
          (a .upper-inhab)

        interval : Ξ£[ n β β ] (Β¬ P n) Γ P (suc n)
        interval = findInterval decP Β¬P0 βPn

      archimedes'' : Ξ£[ r β K ] (Β¬ r β a .upper) Γ (p β€ r) Γ (r + Ξ΅) β a .upper
      archimedes'' = _ , interval .snd .fst , +-rPosββ₯ (nβqβ₯0 (interval .fst) Ξ΅ Ξ΅>0) ,
        subst (_β a .upper)
          ((Ξ» i β p + sucnβqβ‘nβq+q (interval .fst) Ξ΅ i) β +Assoc _ _ _)
          (interval .snd .snd)


    module _
      (p : K)(Β¬pβupper : Β¬ p β a .upper)
      (q : K)(q<p : q < p)
      where

      private
        >-exchange : {a b c : K} β a - b > c β a - c > b
        >-exchange {a = a} {b = b} {c = c} a-b>c =
          transport (Ξ» i β helper3 a b c i > helper4 b c i) (+-rPres< {z = b - c} a-b>c)

      archimedes''' :
        β₯ Ξ£[ r β K ] Ξ£[ s β K ] (Β¬ s β a .upper) Γ (q < r) Γ (r < s) Γ (r + Ξ΅) β a .upper β₯β
      archimedes''' =
        let (r , Β¬rβupper , pβ€r , r+Ξ΅βupper) = archimedes'' p Β¬pβupper in
        Prop.map
        (Ξ» (t , t<r+Ξ΅ , tβupper) β
          let r-q = r - q
              r+Ξ΅-t = (r + Ξ΅) - t
              r-q>0 : r-q > 0r
              r-q>0 = >βDiff>0 (<β€-trans q<p pβ€r)
              r+Ξ΅-t>0 : r+Ξ΅-t > 0r
              r+Ξ΅-t>0 = >βDiff>0 t<r+Ξ΅
              (u , u>0 , u<r-q , u<r+Ξ΅-t) = min2 r-q>0 r+Ξ΅-t>0
              r+Ξ΅-u = (r + Ξ΅) - u
              r-u = r - u
              r-u+Ξ΅ = (r - u) + Ξ΅
              r-u<r : r-u < r
              r-u<r = -rPosβ< u>0
              r-u>q : r-u > q
              r-u>q = >-exchange u<r-q
              r-u+Ξ΅>t : r-u+Ξ΅ > t
              r-u+Ξ΅>t = subst (_> t) (helper2 r u Ξ΅) (>-exchange u<r+Ξ΅-t)
          in  r-u , r , Β¬rβupper , r-u>q , r-u<r , a .upper-close _ _ tβupper r-u+Ξ΅>t)
        (a .upper-round _ r+Ξ΅βupper)


  archimedes' : (a : π)(Ξ΅ : K)(Ξ΅>0 : Ξ΅ > 0r)
    β (p : K)  β Ξ£[ s β K ] ((q : K) β q β a .upper β s < q) Γ (p < s)
    β β₯ Ξ£[ r β K ] Ξ£[ s β K ] ((q : K) β q β a .upper β s < q) Γ (p < r) Γ (r < s) Γ (r + Ξ΅) β a .upper β₯β
  archimedes' a Ξ΅ Ξ΅>0 p (s , s<qβupper , p<s) =
    Prop.map
    (Ξ» (r , s , Β¬sβupper , q<r , r<s , r+Ξ΅βupper) β
        r , s , Β¬βupperβ<upper a _ Β¬sβupper , q<r , r<s , r+Ξ΅βupper)
    (archimedes''' a Ξ΅ Ξ΅>0 s (<upperβΒ¬βupper a _ s<qβupper) p p<s)

  archimedes : (a : π)(Ξ΅ : K)(Ξ΅>0 : Ξ΅ > 0r)
    β β₯ Ξ£[ r β K ] Ξ£[ s β K ] ((q : K) β q β a .upper β s < q) Γ (r < s) Γ (r + Ξ΅) β a .upper β₯β
  archimedes a Ξ΅ Ξ΅>0 = Prop.rec squashβ
    (Ξ» (q , q<rβupper) β Prop.map
      (Ξ» (r , s , s<tβupper , p<r , r<s , r+Ξ΅βupper) β
          r , s , s<tβupper , r<s , r+Ξ΅βupper)
      (archimedes' a Ξ΅ Ξ΅>0 (q - 1r) (q , q<rβupper , q-1<q)))
    (a .lower-inhab)
