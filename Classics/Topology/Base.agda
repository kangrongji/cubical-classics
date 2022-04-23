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

open import Classics.Axioms
open import Classics.Preliminary.Logic
open import Classics.Foundations.Powerset

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ
    Y : Type ℓ'

module Topology (decide : LEM) where

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
    Closed A = Open (∁ A)

    isOpenSubSet : Subset → Type _
    isOpenSubSet U = U ∈ Open

    isClosedSubSet : Subset → Type _
    isClosedSubSet A = ∁ A ∈ Open

    -- Open coverings

    _covers_ : ℙ Subset → Subset → Type _
    _covers_ 𝒰 A = A ⊆ union 𝒰 × 𝒰 ⊆ Open

    union∈Open : {𝒰 : ℙ Subset} → 𝒰 ⊆ Open → union 𝒰 ∈ Open
    union∈Open = X .∪-close

    -- Neighbourhood around a given point

    ℕbh : X .set → ℙ Subset
    ℕbh x A = A x and X .openset A

    N∈ℕbhx→x∈N : {x : X .set}{N : Subset} → N ∈ ℕbh x → x ∈ N
    N∈ℕbhx→x∈N = {!!}

    N∈ℕbhx→N∈Open : {x : X .set}{N : Subset} → N ∈ ℕbh x → N ∈ Open
    N∈ℕbhx→N∈Open = {!!}

    getℕbh : {x : X .set}{N : Subset} → x ∈ N → N ∈ Open → N ∈ ℕbh x
    getℕbh = {!!}

    total∈ℕbh : {x : X .set} → total ∈ ℕbh x
    total∈ℕbh = {!!}

    ℕbh∩ : {x : X .set}{U V : Subset} → U ∈ ℕbh x → V ∈ ℕbh x → U ∩ V ∈ ℕbh x
    ℕbh∩ = {!!}


    -- Inside interior of some someset

    _Σ∈∘_ : (x : X .set) → (U : Subset) → Type _
    x Σ∈∘ U = Σ[ N ∈ Subset ] (N ∈ ℕbh x) × N ⊆ U

    -- It reads "the point x is inside the interior of U"
    -- or "x is an interior point of U".
    _∈∘_ : (x : X .set) → (U : Subset) → Type _
    x ∈∘ U = ∥ x Σ∈∘ U ∥

    ∈→∈∘ : {x : X .set}{U : Subset} → U ∈ Open → x ∈ U → x ∈∘ U
    ∈→∈∘ {U = U} U∈Open x∈U = ∣ _ , getℕbh x∈U U∈Open , ⊆-refl {A = U} ∣

    -- If every point of a subset U is its interior point,
    -- the subset U is open subset.
    ℕbhCriterionOfOpenness : {U : Subset} → ((x : X .set) → x ∈ U → x ∈∘ U) → U ∈ Open
    ℕbhCriterionOfOpenness {U = U} p = U∈Open
      where
      P : Subset → hProp _
      P N = ∥ Σ[ x ∈ X .set ] (N ∈ ℕbh x) × N ⊆ U ∥ , squash

      𝒰 : ℙ Subset
      𝒰 = sub P

      rec-helper1 : {N : Subset} → ∥ Σ[ x ∈ X .set ] (N ∈ ℕbh x) × N ⊆ U ∥ → N ∈ Open
      rec-helper1 = Prop.rec (isProp∈ {A = Open}) λ (_ , p , _) → N∈ℕbhx→N∈Open p

      𝒰⊆Open : 𝒰 ⊆ Open
      𝒰⊆Open p = rec-helper1 (∈→Inhab P p)

      𝕌 : Subset
      𝕌 = union 𝒰

      𝕌∈Open : 𝕌 ∈ Open
      𝕌∈Open = X .∪-close 𝒰⊆Open

      rec-helper2 : {N : Subset} → ∥ Σ[ x ∈ X .set ] (N ∈ ℕbh x) × N ⊆ U ∥ → N ⊆ U
      rec-helper2 = Prop.rec isProp⊆ λ (_ , _ , p) → p

      N∈𝒰→N⊆U : (N : Subset) → N ∈ 𝒰 → N ⊆ U
      N∈𝒰→N⊆U _ p = rec-helper2 (∈→Inhab P p)

      𝕌⊆U : 𝕌 ⊆ U
      𝕌⊆U = union⊆ N∈𝒰→N⊆U

      U⊆𝕌 : U ⊆ 𝕌
      U⊆𝕌 x∈U = ∈union
        (Prop.map (λ (N , N∈ℕx , N⊆U) → N , N∈ℕbhx→x∈N N∈ℕx , Inhab→∈ P ∣ _ , N∈ℕx , N⊆U ∣) (p _ x∈U))

      𝕌≡U : 𝕌 ≡ U
      𝕌≡U = bi⊆→≡ 𝕌⊆U U⊆𝕌

      U∈Open : U ∈ Open
      U∈Open = subst (_∈ Open) 𝕌≡U 𝕌∈Open


    -- Separating a point from a subset using open sets

    ΣSep : (x : X .set) → Subset → Type _
    ΣSep x A = Σ[ V ∈ Subset ] (V ∈ ℕbh x) × (A ∩ V ≡ ∅)

    ΣSep⊆ : {x : X .set}{A B : Subset} → A ⊆ B → ΣSep x B → ΣSep x A
    ΣSep⊆ = {!!}

    -- It reads as "there merely exists a neighbourhood of x that is separated from A".
    Sep : (x : X .set) → Subset → Type _
    Sep x A = ∥ ΣSep x A ∥

    Sep⊆ : {x : X .set}{A B : Subset} → A ⊆ B → Sep x B → Sep x A
    Sep⊆ A⊆B = Prop.map (ΣSep⊆ A⊆B)

    Sep→∈∘∁ : {x : X .set}{A : Subset} → Sep x A → x ∈∘ (∁ A)
    Sep→∈∘∁ = {!!}

    -- It reads as "there merely exists neighbourhood of x and A respectively that don't intersect with each other",
    -- or "point x and subset A are separating by open sets"
    SepOpen : (x : X .set) → Subset → Type _
    SepOpen x A = ∥ Σ[ U ∈ Subset ] Σ[ V ∈ Subset ] (U ∈ Open) × A ⊆ U × (V ∈ ℕbh x) × (A ∩ V ≡ ∅) ∥

    SepOpen⊆ : {x : X .set}{A U : Subset} → A ⊆ U → Sep x U → SepOpen x A
    SepOpen⊆ = {!!}

    SepOpen→Sep : {x : X .set}{A : Subset} → SepOpen x A → Sep x A
    SepOpen→Sep = {!!}


    -- A subset K ⊆ X is closed if for any x ∉ K, there merely exists neigubourhood of x separating from K.
    SepCriterionOfClosedness : {K : Subset} → ((x : X .set) → x ∉ K → Sep x K) → K ∈ Closed
    SepCriterionOfClosedness {K = K} sep = ℕbhCriterionOfOpenness x∉K→x∈∘∁K
      where
      x∉K→x∈∘∁K : (x : X .set) → x ∈ (∁ K) → x ∈∘ (∁ K)
      x∉K→x∈∘∁K x x∈∁K = Sep→∈∘∁ (sep x (∈∁→∉ {A = K} x∈∁K))


    -- Given a finite covering 𝒰
    -- such that for any open U ∈ 𝒰, there merely exists a neighbourhood of x not intersecting with U,
    -- then there merely exists a neighbourhood of x that is not intersecting with the union of opens in 𝒰.
    unionSep : (x : X .set)
      (𝒰 : ℙ Subset)(𝒰⊆Open : 𝒰 ⊆ Open)
      (sep : (U : Subset) → U ∈ 𝒰 → Sep x U)
      → isFinSubset 𝒰 → Sep x (union 𝒰)
    unionSep x 𝒰 _ _ isfin∅ = ∣ total , total∈ℕbh {x = x} , ∩-rUnit (union 𝒰) ∙ union∅ ∣
    unionSep x 𝒰 𝒰⊆Open sep (isfinsuc U {A = 𝒰₀} fin𝒰₀) = subst (Sep x) (sym union∪[A]) sep𝕌₀∪U
      where
      𝕌₀ : Subset
      𝕌₀ = union 𝒰₀

      𝒰₀⊆𝒰 : 𝒰₀ ⊆ 𝒰
      𝒰₀⊆𝒰 = ∪-left⊆ 𝒰₀ [ U ]

      𝒰₀⊆Open : 𝒰₀ ⊆ Open
      𝒰₀⊆Open = ⊆-trans {A = 𝒰₀} 𝒰₀⊆𝒰 𝒰⊆Open

      𝕌₀∈Open : 𝕌₀ ∈ Open
      𝕌₀∈Open = union∈Open 𝒰₀⊆Open

      -- TODO : Make a solver to deal with these problems.
      ∪∅-helper : {A B C D : Subset} → A ∩ C ≡ ∅ → B ∩ D ≡ ∅ → (A ∪ B) ∩ (C ∩ D) ≡ ∅
      ∪∅-helper {A = A} {B = B} {C = C} {D = D} A∩C≡∅ B∩D≡∅ =
          ∩-∪-lDist _ _ _
        ∙ (λ i → ∩-Assoc A C D i ∪ (B ∩ ∩-Comm C D i))
        ∙ (λ i → ((A ∩ C) ∩ D) ∪ ∩-Assoc B D C i)
        ∙ (λ i → (A∩C≡∅ i ∩ D) ∪ (B∩D≡∅ i ∩ C))
        ∙ (λ i → ∩-lZero D i ∪ ∩-lZero C i)
        ∙ ∪-Idem _

      ind-Sep-helper : (A B : Subset) → A ∈ Open → B ∈ Open → ΣSep x A → ΣSep x B → ΣSep x (A ∪ B)
      ind-Sep-helper _ _ _ _ (VA , VA∈Nx , VA∅) (VB , VB∈Nx , VB∅) =
        VA ∩ VB , ℕbh∩ VA∈Nx VB∈Nx , ∪∅-helper VA∅ VB∅

      ind-Sep : (A B : Subset) → A ∈ Open → B ∈ Open → _
      ind-Sep A B p q = Prop.map2 (ind-Sep-helper A B p q)

      sep𝕌₀ : Sep x 𝕌₀
      sep𝕌₀ = unionSep _ _ 𝒰₀⊆Open (λ U U∈𝒰₀ → sep U (∈⊆-trans {A = 𝒰₀} U∈𝒰₀ 𝒰₀⊆𝒰)) fin𝒰₀

      U∈𝒰 : U ∈ 𝒰
      U∈𝒰 = [A]⊆S→A∈S (∪-right⊆ 𝒰₀ [ U ])

      U∈Open : U ∈ Open
      U∈Open = ∈⊆-trans {A = 𝒰} U∈𝒰 𝒰⊆Open

      sep[U] : Sep x U
      sep[U] = sep U U∈𝒰

      sep𝕌₀∪U : Sep x (𝕌₀ ∪ U)
      sep𝕌₀∪U = ind-Sep _ _ 𝕌₀∈Open U∈Open sep𝕌₀ sep[U]


    -- Compactness

    isCompactSubset : Subset → Type _
    isCompactSubset K =
      (𝒰 : ℙ Subset) → 𝒰 covers K → ∥ Σ[ 𝒰₀ ∈ ℙ Subset ] 𝒰₀ ⊆ 𝒰 × isFinSubset 𝒰₀ × 𝒰₀ covers K ∥

    isCompact : Type _
    isCompact = isCompactSubset total

    isHausdorff : Type _
    isHausdorff =
      {x y : X .set} → ¬ x ≡ y → ∥ Σ[ U ∈ Subset ] Σ[ V ∈ Subset ] (U ∈ ℕbh x) × (V ∈ ℕbh y) × (U ∩ V ≡ ∅) ∥


    module _
      (haus : isHausdorff) where

      -- In a Hausdorff space X,
      -- point x ∈ X and subset K ⊆ X are separating by open sets
      -- if x ∉ K and K is compact.
      sepOpenCompact : {x : X .set}{K : Subset} → isCompactSubset K → x ∉ K → SepOpen x K
      sepOpenCompact {x = x₀} {K = K} iscmpt x₀∉K = sepOpen
        where
        P : Subset → hProp _
        P U = ∥ Σ[ x ∈ X .set ] (x ∈ K) × (U ∈ ℕbh x) × (Sep x₀ U) ∥ , squash

        𝒰 : ℙ Subset
        𝒰 = sub P

        𝒰⊆Open : 𝒰 ⊆ Open
        𝒰⊆Open p =
          Prop.rec (isProp∈ {A = Open}) (λ (_ , _ , q , _) → N∈ℕbhx→N∈Open q) (∈→Inhab P p)

        𝕌 : Subset
        𝕌 = union 𝒰

        -- A shuffle of propositions
        K⊆𝕌 : K ⊆ 𝕌
        K⊆𝕌 x∈K =
          Prop.rec (isProp∈ {A = 𝕌})
          (λ (U , V , U∈ℕx , V∈ℕx₀ , U∩V≡∅) →
             ∈union ∣ U , N∈ℕbhx→x∈N U∈ℕx , Inhab→∈ P ∣ _ , x∈K , U∈ℕx , ∣ V , V∈ℕx₀ , U∩V≡∅ ∣ ∣ ∣)
          (haus (∈∉→≢ x∈K x₀∉K))

        𝒰-covers-K : 𝒰 covers K
        𝒰-covers-K = K⊆𝕌 , 𝒰⊆Open

        𝕌∈Open : 𝕌 ∈ Open
        𝕌∈Open = union∈Open 𝒰⊆Open

        -- Another shuffle of propositions
        ∃𝒰₀ : ∥ Σ[ 𝒰₀ ∈ ℙ Subset ] 𝒰₀ ⊆ Open × isFinSubset 𝒰₀ × 𝒰₀ covers K × ((U : Subset) → U ∈ 𝒰₀ → Sep x₀ U) ∥
        ∃𝒰₀ =
          Prop.map
          (λ (𝒰₀ , 𝒰₀⊆𝒰 , fin𝒰₀ , 𝒰₀covK) →
              𝒰₀ , ⊆-trans {C = Open} 𝒰₀⊆𝒰 𝒰⊆Open , fin𝒰₀ , 𝒰₀covK ,
              λ U U∈𝒰₀ → Prop.rec squash (λ (_ , _ , _ , sep) → sep) (∈→Inhab P (∈⊆-trans {B = 𝒰} U∈𝒰₀ 𝒰₀⊆𝒰)))
          (iscmpt _ 𝒰-covers-K)

        sepOpen : SepOpen x₀ K
        sepOpen = Prop.rec squash
          (λ (_ , 𝒰₀⊆Open , fin⊆𝒰₀ , 𝒰₀covK , sep)
              →  SepOpen⊆ (𝒰₀covK .fst) (unionSep _ _ 𝒰₀⊆Open sep fin⊆𝒰₀)) ∃𝒰₀


      isCompactSubset→isClosedSubSet : {K : Subset} → isCompactSubset K → isClosedSubSet K
      isCompactSubset→isClosedSubSet iscmpt = SepCriterionOfClosedness (λ _ x∉K → SepOpen→Sep (sepOpenCompact iscmpt x∉K))
