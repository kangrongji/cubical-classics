{-

Hausdorff Space

This file contains:
- Definition of Hausdorff space;
- Point and compact subset can be separated by open set in Hausdorff space;
- Compact subset in Hausdorff space is closed.

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Hausdorff where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Axioms
open import Classical.Foundations.Powerset

open import Classical.Topology.Base
open import Classical.Topology.Properties
open import Classical.Topology.Neighbourhood

private
  variable
    β : Level


module _ β¦ π€ : Oracle β¦ where

  open Topology


  -- As is usually formulated, a topological space X is Hausdorff,
  -- if any two different points x y of X merely have neighbourhoods that do not intersect.

  record isHausdorff {X : Type β} β¦ π― : Topology X β¦ : Type β where
    field
      separate : {x y : X} β Β¬ x β‘ y β β₯ Ξ£[ U β β X ] Ξ£[ V β β X ] (U β βbh x) Γ (V β βbh y) Γ (U β© V β‘ β) β₯β


  module _ {X : Type β} β¦ π― : Topology X β¦ β¦ haus : isHausdorff β¦ where

      open isHausdorff haus

      {-

        Corollaries of Hausdorff-ness

      -}

      -- In a Hausdorff space X,
      -- point x β X and subset K β X are separating by open sets
      -- if x β K and K is compact.

      sepOpenCompact : {x : X}{K : β X} β isCompactSub K β x β K β SepOpen x K
      sepOpenCompact {x = xβ} {K = K} takefin xββK = sepOpen
        where
        P : β X β hProp _
        P U = β₯ Ξ£[ x β X ] (x β K) Γ (U β βbh x) Γ (Sep xβ U) β₯β , squashβ

        π° : β β X
        π° = specify P

        π°βOpen : π° β Open
        π°βOpen p =
          Prop.rec (isPropβ Open) (Ξ» (_ , _ , q , _) β NββbhxβNβOpen q) (ββInhab P p)

        π : β X
        π = union π°

        -- A shuffle of propositions
        Kβπ : K β π
        Kβπ xβK =
          Prop.rec (isPropβ π)
          (Ξ» (U , V , Uββx , Vββxβ , Uβ©Vβ‘β) β
             βββunion β£ U , NββbhxβxβN Uββx , Inhabββ P β£ _ , xβK , Uββx , β£ V , Vββxβ , Uβ©Vβ‘β β£β β£β β£β)
          (separate (ββββ’ xβK xββK))

        π°-covers-K : π° covers K
        π°-covers-K = Kβπ , π°βOpen

        πβOpen : π β Open
        πβOpen = unionβOpen π°βOpen

        -- Another shuffle of propositions
        βπ°β : β₯ Ξ£[ π°β β β β X ] π°β β Open Γ isFinSub π°β Γ π°β covers K Γ ((U : β X) β U β π°β β Sep xβ U) β₯β
        βπ°β =
          Prop.map
          (Ξ» (π°β , π°ββπ° , finπ°β , π°βcovK) β
              π°β , β-trans {C = Open} π°ββπ° π°βOpen , finπ°β , π°βcovK ,
              Ξ» U Uβπ°β β Prop.rec squashβ (Ξ» (_ , _ , _ , sep) β sep) (ββInhab P (ββ-trans {B = π°} Uβπ°β π°ββπ°)))
          (takefin π°-covers-K)

        sepOpen : SepOpen xβ K
        sepOpen = Prop.rec squashβ
          (Ξ» (_ , π°ββOpen , finβπ°β , π°βcovK , sep)
              β  SepOpenβ (unionβOpen π°ββOpen) (π°βcovK .fst) (unionSep _ _ π°ββOpen sep finβπ°β)) βπ°β


      -- Compact subset of Hausdorff space is closed.

      isCompactSubβisClosedSub : {K : β X} β isCompactSub K β isClosedSub K
      isCompactSubβisClosedSub takefin =
        SepCriterionOfClosedness (Ξ» _ xβK β SepOpenβSep (sepOpenCompact takefin xβK))
