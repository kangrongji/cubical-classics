{-

Topological Space

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classics.Topology.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism hiding (section)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Data.Sigma
open import Cubical.Data.Bool

open import Cubical.HITs.PropositionalTruncation as Prop hiding (map)

open import Cubical.Relation.Nullary

open import Classics.Axioms.Choice
open import Classics.Axioms.ExcludedMiddle
open import Classics.Foundations.Powerset

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ
    Y : Type ℓ'

module Topology (decide : LEM)(choice : AC) where

  open AxiomOfChoice choice
  open Powerset decide

  -- Definitions

  record TopologicalSpace (ℓ : Level) : Type (ℓ-suc ℓ) where
    field
      set   : Type ℓ
      isset : isSet set
      openset : ℙ (ℙ set)
      has-∅     : ∅     ∈ openset
      has-total : total ∈ openset
      ∩-close : {A B : ℙ set}   → A ∈ openset → B ∈ openset → A ∩ B ∈ openset
      ∪-close : {S : ℙ (ℙ set)} → S ⊆ openset → union S ∈ openset

  open TopologicalSpace

  record ContinuousMap {ℓ ℓ' : Level}
    (X : TopologicalSpace ℓ)(Y : TopologicalSpace ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      map : X .set → Y .set
      presopen : (U : ℙ (Y .set)) → U ∈ Y .openset → preimage map U ∈ X .openset

  open ContinuousMap

  -- Basic properties of topological spaces

  module _
    (X : TopologicalSpace ℓ) where

    -- Some convenient naming

    Subset : Type _
    Subset = ℙ (X .set)

    Open : ℙ Subset
    Open = X .openset

    Closed : ℙ Subset
    Closed A = X .openset (∁ A)

    isOpenSubSet : Subset → Type _
    isOpenSubSet U = U ∈ X .openset

    isClosedSubSet : Subset → Type _
    isClosedSubSet A = ∁ A ∈ X .openset

    -- Open covers

    _covers_ : ℙ Subset → Subset → Type _
    _covers_ 𝒰 A = A ⊆ union 𝒰 × 𝒰 ⊆ X .openset

    union∈Open : {𝒰 : ℙ Subset} → 𝒰 ⊆ Open → union 𝒰 ∈ Open
    union∈Open = {!!}

    -- Neighbourhood around a given point

    ℕbh : X .set → ℙ Subset
    ℕbh x A = A x and X .openset A

    N∈ℕbhx→x∈N : {x : X .set}{N : Subset} → N ∈ ℕbh x → x ∈ N
    N∈ℕbhx→x∈N = {!!}

    getℕbh : {x : X .set}{N : Subset} → x ∈ N → N ∈ Open → N ∈ ℕbh x
    getℕbh = {!!}

    total∈ℕbh : {x : X .set} → total ∈ ℕbh x
    total∈ℕbh = {!!}

    ℕbh∩ : {x : X .set}{U V : Subset} → U ∈ ℕbh x → V ∈ ℕbh x → U ∩ V ∈ ℕbh x
    ℕbh∩ = {!!}


    -- Inside interior of some someset

    _∈∙_ : (x : X .set) → (U : Subset) → Type _
    x ∈∙ U = Σ[ N ∈ Subset ] (N ∈ ℕbh x) × N ⊆ U

    _∈∘_ : (x : X .set) → (U : Subset) → Type _
    x ∈∘ U = ∥ x ∈∙ U ∥

    isProp∈∙ : {x : X .set}{U : Subset} → isProp (x ∈∙ U)
    isProp∈∙ = {!!}

    ℕbhCriterionOfOpenness : (U : Subset) → ((x : X .set) → x ∈ U → x ∈∘ U) → U ∈ X .openset
    ℕbhCriterionOfOpenness U p = U∈Open
      where
      P : Subset → hProp _
      P N = ∥ Σ[ x ∈ X .set ] (N ∈ ℕbh x) × N ⊆ U ∥ , squash

      𝒰 : ℙ Subset
      𝒰 = sub P

      helper : {N : Subset} → ∥ Σ[ x ∈ X .set ] (N ∈ ℕbh x) × N ⊆ U ∥ → N ∈ X .openset
      helper = {!!}

      𝒰⊆Open : 𝒰 ⊆ X .openset
      𝒰⊆Open p = helper (∈→Inhab P p)

      𝕌 : Subset
      𝕌 = union 𝒰

      𝕌∈Open : 𝕌 ∈ X .openset
      𝕌∈Open = X .∪-close 𝒰⊆Open

      helper' : {N : Subset} → ∥ Σ[ x ∈ X .set ] (N ∈ ℕbh x) × N ⊆ U ∥ → N ⊆ U
      helper' = {!!}

      N∈𝒰→N⊆U : (N : Subset) → N ∈ 𝒰 → N ⊆ U
      N∈𝒰→N⊆U _ p = helper' (∈→Inhab P p)

      𝕌⊆U : 𝕌 ⊆ U
      𝕌⊆U = union⊆ N∈𝒰→N⊆U

      helper'' : (x : X .set) → x ∈ U → Σ[ N ∈ Subset ] (N ∈ ℕbh x) × (N ⊆ U)
        → Σ[ N ∈ Subset ] (x ∈ N) × (N ∈ 𝒰)
      helper'' x x∈U (N , N∈Nx , N⊆U) = N , N∈ℕbhx→x∈N N∈Nx , Inhab→∈ P ∣ x , N∈Nx , N⊆U ∣

      helper''' : ∥ ((x : X .set) → x ∈ U → Σ[ N ∈ Subset ] (N ∈ ℕbh x) × (N ⊆ U)) ∥
        → (x : X .set) → x ∈ U → ∥ Σ[ N ∈ Subset ] (x ∈ N) × (N ∈ 𝒰) ∥
      helper''' = {!!}

      choice-helper : _
      choice-helper =
        choice2 (X .isset)
          (λ _ → isProp→isSet (isProp∈ {A = U}))
          (λ _ _ → isProp→isSet isProp∈∙) p

      U⊆𝕌 : U ⊆ 𝕌
      U⊆𝕌 x∈U = ∈union (helper''' choice-helper _ x∈U)

      𝕌≡U : 𝕌 ≡ U
      𝕌≡U = bi⊆→≡ 𝕌⊆U U⊆𝕌

      U∈Open : U ∈ X .openset
      U∈Open = subst (_∈ X .openset) 𝕌≡U 𝕌∈Open


    -- A technical lemma to construct separating open set

    coverSeparate :
      (x : X .set)(𝒰 : ℙ Subset)(𝒰⊆Open : 𝒰 ⊆ Open)
      (sep : (U : Subset) → U ∈ 𝒰 → ∥ Σ[ V ∈ Subset ] (V ∈ ℕbh x) × (U ∩ V ≡ ∅) ∥)
      → isFinSubset 𝒰 → ∥ Σ[ V ∈ Subset ] (V ∈ ℕbh x) × (union 𝒰 ∩ V ≡ ∅) ∥
    coverSeparate x 𝒰 _ _ isfin∅ = ∣ total , total∈ℕbh {x = x} , ∩-rUnit (union 𝒰) ∙ union∅ ∣
    coverSeparate x 𝒰 𝒰⊆Open sep (isfinsuc U {A = 𝒰₀} fin𝒰₀) = subst Sep (sym union∪[A]) sep𝕌₀∪U
      where
      Sep : Subset → Type _
      Sep A = ∥ Σ[ V ∈ Subset ] (V ∈ ℕbh x) × (A ∩ V ≡ ∅) ∥

      𝕌₀ : Subset
      𝕌₀ = union 𝒰₀

      𝒰₀⊆𝒰 : 𝒰₀ ⊆ 𝒰
      𝒰₀⊆𝒰 = ∪-left⊆ 𝒰₀ [ U ]

      𝒰₀⊆Open : 𝒰₀ ⊆ Open
      𝒰₀⊆Open = ⊆-trans {A = 𝒰₀} 𝒰₀⊆𝒰 𝒰⊆Open

      𝕌₀∈Open : 𝕌₀ ∈ Open
      𝕌₀∈Open = union∈Open 𝒰₀⊆Open

      ∪∅-helper : (A B C D : Subset) → A ∩ C ≡ ∅ → B ∩ D ≡ ∅ → (A ∪ B) ∩ (C ∩ D) ≡ ∅
      ∪∅-helper = {!!}

      ind-Sep-helper : (A B : Subset) → A ∈ Open → B ∈ Open
        → Σ[ V ∈ Subset ] (V ∈ ℕbh x) × (A ∩ V ≡ ∅)
        → Σ[ V ∈ Subset ] (V ∈ ℕbh x) × (B ∩ V ≡ ∅)
        → Σ[ V ∈ Subset ] (V ∈ ℕbh x) × ((A ∪ B) ∩ V ≡ ∅)
      ind-Sep-helper _ _ _ _ (VA , VA∈Nx , VA∅) (VB , VB∈Nx , VB∅) =
        VA ∩ VB , ℕbh∩ VA∈Nx VB∈Nx , ∪∅-helper _ _ _ _ VA∅ VB∅

      ind-Sep : (A B : Subset) → A ∈ Open → B ∈ Open → _
      ind-Sep A B p q = Prop.map2 (ind-Sep-helper A B p q)

      sep𝕌₀ : Sep 𝕌₀
      sep𝕌₀ = coverSeparate _ _ 𝒰₀⊆Open (λ U U∈𝒰₀ → sep U (∈⊆-trans {A = 𝒰₀} U∈𝒰₀ 𝒰₀⊆𝒰)) fin𝒰₀

      U∈𝒰 : U ∈ 𝒰
      U∈𝒰 = [A]⊆S→A∈S (∪-right⊆ 𝒰₀ [ U ])

      U∈Open : U ∈ Open
      U∈Open = ∈⊆-trans {A = 𝒰} U∈𝒰 𝒰⊆Open

      sep[U] : Sep U
      sep[U] = sep U U∈𝒰

      sep𝕌₀∪U : Sep (𝕌₀ ∪ U)
      sep𝕌₀∪U = ind-Sep _ _ 𝕌₀∈Open U∈Open sep𝕌₀ sep[U]


    -- Compactness

    isCompactSubset : Subset → Type _
    isCompactSubset K =
      (𝒰 : ℙ Subset) → 𝒰 covers K → ∥ Σ[ 𝒰₀ ∈ ℙ Subset ] 𝒰₀ ⊆ 𝒰 × isFinSubset 𝒰₀ × 𝒰₀ covers K ∥

    isCompact : Type _
    isCompact = isCompactSubset total

    isHausdorff : Type _
    isHausdorff =
      (x y : X .set) → ∥ Σ[ U ∈ Subset ] Σ[ V ∈ Subset ] (U ∈ ℕbh x) × (V ∈ ℕbh y) × (U ∩ V ≡ ∅) ∥

    private
      module _
        (haus : isHausdorff)
        (K : Subset)(iscmpt : isCompactSubset K)
        (x₀ : X .set) where

        P : Subset → hProp _
        P U = ∥ Σ[ x ∈ X .set ] (x ∈ K) × (U ∈ ℕbh x) × (Σ[ V ∈ Subset ] (V ∈ ℕbh x₀) × (U ∩ V ≡ ∅)) ∥ , squash

        𝒰 : ℙ Subset
        𝒰 = sub P

        𝒰⊆Open : 𝒰 ⊆ X .openset
        𝒰⊆Open p = {!!}

        𝒰-covers-K : 𝒰 covers K
        𝒰-covers-K = {!!}

        𝕌 : Subset
        𝕌 = union 𝒰

        𝕌∈Open : 𝕌 ∈ X .openset
        𝕌∈Open = X .∪-close 𝒰⊆Open

        ∃𝒰₀' : ∥ Σ[ 𝒰₀ ∈ ℙ Subset ] 𝒰₀ ⊆ 𝒰 × isFinSubset 𝒰₀ × 𝒰₀ covers K ∥
        ∃𝒰₀' = iscmpt _ 𝒰-covers-K

        ∃𝒰₀ :
          ∥ Σ[ 𝒰₀ ∈ ℙ Subset ]
                𝒰₀ ⊆ Open
              × isFinSubset 𝒰₀
              × 𝒰₀ covers K
              × ((U : Subset) → U ∈ 𝒰₀ → Σ[ V ∈ Subset ] (V ∈ ℕbh x₀) × (U ∩ V ≡ ∅)) ∥
        ∃𝒰₀ = {!!}

    isCompactSubset→isClosedSubSet : isHausdorff → (K : Subset) → isCompactSubset K → isClosedSubSet K
    isCompactSubset→isClosedSubSet p K compt = {!!}
