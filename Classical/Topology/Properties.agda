{-

This file contains:
- The notion of closed subset;
- Basics of open covering;
- Basics of compactness.

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms

open import Classical.Foundations.Powerset
open import Classical.Topology.Base

private
  variable
    β : Level


module _ β¦ π€ : Oracle β¦ where

  open Topology


  module _ {X : Type β} β¦ π― : Topology X β¦ where

    {-

      The Open and Closed Subset

    -}

    Open : β β X
    Open = π― .openset

    Closed : β β X
    Closed A = Open (β A)

    isOpenSub : β X β Type _
    isOpenSub U = U β Open

    isClosedSub : β X β Type _
    isClosedSub A = β A β Open

    isOpenSubβ : {A : β X} β isClosedSub A β isOpenSub (β A)
    isOpenSubβ p = p

    isClosedSubβ : {A : β X} β isOpenSub A β isClosedSub (β A)
    isClosedSubβ = subst (_β Open) (sym (β-Unip _))


    {-

      Open Covering

    -}

    -- We say `π° covers K` if the members of π° are all open, and their union contains K.

    _covers_ : β β X β β X β Type _
    _covers_ π° A = A β union π° Γ π° β Open

    unionβOpen : {π° : β β X} β π° β Open β union π° β Open
    unionβOpen = π― .βͺ-close

    βcover : {x : X}{A : β X}{π° : β β X} β x β A β π° covers A β β₯ Ξ£[ U β β X ] x β U Γ U β π° β₯β
    βcover xβA π°covA = βunionββ (π°covA .fst xβA)


    {-

      Compactness

    -}

    -- A subset K is compact,
    -- if for any open covering π° of K,
    -- there always merely exists a finite subcover of π°.

    isCompactSub : β X β Type _
    isCompactSub K =
      {π° : β β X} β π° covers K β β₯ Ξ£[ π°β β β β X ] π°β β π° Γ isFinSub π°β Γ π°β covers K β₯β

    isCompact : Type _
    isCompact = isCompactSub total

    isPropIsCompactSub : {A : β X} β isProp (isCompactSub A)
    isPropIsCompactSub = isPropImplicitΞ  (Ξ» _ β isPropΞ  (Ξ» _ β squashβ))


    -- A closed subset that is contained in certain compact subset is itself compact.

    isClosedInCompactβisCompact :
      {A K : β X} β A β K β isClosedSub A β isCompactSub K β isCompactSub A
    isClosedInCompactβisCompact {A = A} {K = K} AβK βAβOpen takefinK {π° = π°} π°covA = βπ°β
      where

      π°+βA : β β X
      π°+βA = π° βͺ [ β A ]

      βͺ-helper : {x : X} β (x β union π°) β (x β β A) β x β union π°+βA
      βͺ-helper (inl xββͺπ°) = unionβͺ-leftβ xββͺπ°
      βͺ-helper {x = x} (inr xβ[βA]) = unionβͺ-rightβ (subst (x β_) (sym union[A]) xβ[βA])

      π°+βA-covK : π°+βA covers K
      π°+βA-covK .fst {x = x} xβK = case-split (dichotomyβ x A)
        where
        case-split : Dichotomyβ x A β _
        case-split (yeah xβA) = βͺ-helper (inl (π°covA .fst xβA))
        case-split (nope xβA) = βͺ-helper (inr (ββββ {A = A} xβA))
      π°+βA-covK .snd = ββββͺ {C = Open} (π°covA .snd) (AβSβ[A]βS {S = Open} βAβOpen)

      aβU+Uβπ°+βAβUβπ° : {x : X}{U : β X} β x β A β x β U β U β π°+βA β U β π°
      aβU+Uβπ°+βAβUβπ° {x = x} {U = U} xβA xβU Uβπ°+βA = case-split (βAβͺBββA+βB π° [ β A ] Uβπ°+βA)
        where
        case-split : (U β π°) β (U β [ β A ]) β U β π°
        case-split (inl Uβπ°) = Uβπ°
        case-split (inr Uβ[βA]) = Empty.rec (ββΒ¬β {A = A} (ββββ {A = A} xββA) xβA)
          where
          xββA : x β β A
          xββA = Prop.rec (isPropβ (β A))
            (Ξ» βAβ‘U β subst (x β_) (sym βAβ‘U) xβU)
            (yβ[x]ββ₯xβ‘yβ₯ Uβ[βA])

      module _ (π°' : β β X)(π°'βπ°+βA : π°' β π°+βA)(finπ°' : isFinSub π°')(π°'covK : π°' covers K) where

        cov-prop : β X β hProp _
        cov-prop U = β₯ Ξ£[ x β X ] (x β A) Γ (x β U) Γ (U β π°') β₯β , squashβ

        π°β = specify cov-prop

        π°ββπ°' : π°β β π°'
        π°ββπ°' Uβπ°β = Prop.rec (isPropβ π°')
          (Ξ» (x , xβA , xβU , Uβπ°') β Uβπ°')
          (ββInhab cov-prop Uβπ°β)

        π°ββπ° : π°β β π°
        π°ββπ° Uβπ°β = Prop.rec (isPropβ π°)
          (Ξ» (x , xβA , xβU , Uβπ°') β
            aβU+Uβπ°+βAβUβπ° xβA xβU (π°'βπ°+βA Uβπ°'))
          (ββInhab cov-prop Uβπ°β)

        finπ°β : isFinSub π°β
        finπ°β = isFinSubβ π°ββπ°' finπ°'

        π°βcovA : π°β covers A
        π°βcovA .fst {x = x} xβA = βββunion βU
          where
          βU : β₯ Ξ£[ U β β X ] (x β U) Γ (U β π°β) β₯β
          βU = Prop.map
            (Ξ» (U , xβU , Uβπ°') β
              U , xβU , Inhabββ cov-prop β£ x , xβA , xβU , Uβπ°' β£β)
            (βunionββ (π°'covK .fst (AβK xβA)))
        π°βcovA .snd Uβπ°β = π°covA .snd (π°ββπ° Uβπ°β)

        Ξ£π°β : Ξ£[ π°β β β β X ] π°β β π° Γ isFinSub π°β Γ π°β covers A
        Ξ£π°β = π°β , π°ββπ° , finπ°β , π°βcovA

      βπ°β : β₯ Ξ£[ π°β β β β X ] π°β β π° Γ isFinSub π°β Γ π°β covers A β₯β
      βπ°β = Prop.map
        (Ξ» (π°' , π°'βπ°+βA , finπ°' , π°'covK) β
          Ξ£π°β π°' π°'βπ°+βA finπ°' π°'covK)
        (takefinK π°+βA-covK)
