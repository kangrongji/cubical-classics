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

  record ContinuousMap {ℓ ℓ' : Level} (X : TopologicalSpace ℓ)(Y : TopologicalSpace ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      map : X .set → Y .set
      presopen : (U : ℙ (Y .set)) → U ∈ Y .openset → preimage map U ∈ X .openset

  open ContinuousMap

  record Presheaf {ℓ ℓ' : Level} (X : TopologicalSpace ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      section : (U : ℙ (X .set)) → U ∈ X .openset → Type ℓ'
      --restric : {U V : ℙ (X .set)} → U ∈ X .openset → V ∈ X .openset → U ⊆ V → 

  module _
    (X : TopologicalSpace ℓ) where

    Subset : Type _
    Subset = ℙ (X .set)

    SubFamily : Type _
    SubFamily = ℙ (ℙ (X .set))

    closedset : ℙ (ℙ (X .set))
    closedset A = X .openset (compdecideent A)

    isOpen : ℙ (X .set) → Type _
    isOpen U = U ∈ X .openset

    isClosed : ℙ (X .set) → Type _
    isClosed A = compdecideent A ∈ X .openset

    ℕbh : X .set → ℙ (ℙ (X .set))
    ℕbh x A = A x and X .openset A

    N∈ℕbhx→x∈N : {x : X .set}{N : ℙ (X .set)} → N ∈ ℕbh x → x ∈ N
    N∈ℕbhx→x∈N = {!!}

    _covers_ : ℙ (ℙ (X .set)) → ℙ (X .set) → Type _
    _covers_ 𝒰 A = A ⊆ union 𝒰 × 𝒰 ⊆ X .openset

    isCompactSubset : ℙ (X .set) → Type _
    isCompactSubset K =
      (𝒰 : ℙ (ℙ (X .set))) → 𝒰 covers K → ∥ Σ[ 𝒰₀ ∈ ℙ (ℙ (X .set)) ] 𝒰₀ ⊆ 𝒰 × isFinSubset 𝒰₀ × 𝒰₀ covers K ∥

    isCompact : Type _
    isCompact = isCompactSubset total

    isHausdorff : Type _
    isHausdorff =
      (x y : X .set) → ∥ Σ[ U ∈ ℙ (X .set) ] Σ[ V ∈ ℙ (X .set) ] (U ∈ ℕbh x) × (V ∈ ℕbh y) × (U ∩ V ≡ ∅) ∥

    _∈∙_ : (x : X .set) → (U : ℙ (X .set)) → Type _
    x ∈∙ U = Σ[ N ∈ ℙ (X .set) ] (N ∈ ℕbh x) × N ⊆ U

    _∈∘_ : (x : X .set) → (U : ℙ (X .set)) → Type _
    x ∈∘ U = ∥ x ∈∙ U ∥

    isProp∈∙ : {x : X .set}{U : ℙ (X .set)} → isProp (x ∈∙ U)
    isProp∈∙ = {!!}

    private
      module _
        (U : ℙ (X .set)) where

        P : ℙ (X .set) → hProp _
        P N = ∥ Σ[ x ∈ X .set ] (N ∈ ℕbh x) × N ⊆ U ∥ , squash

        𝒰 : ℙ (ℙ (X .set))
        𝒰 = sub P

        helper : {N : ℙ (X .set)} → ∥ Σ[ x ∈ X .set ] (N ∈ ℕbh x) × N ⊆ U ∥ → N ∈ X .openset
        helper = {!!}

        𝒰⊆Open : 𝒰 ⊆ X .openset
        𝒰⊆Open p = helper (∈→Inhab P p)

        𝕌 : ℙ (X .set)
        𝕌 = union 𝒰

        𝕌∈Open : 𝕌 ∈ X .openset
        𝕌∈Open = X .∪-close 𝒰⊆Open

        helper' : {N : ℙ (X .set)} → ∥ Σ[ x ∈ X .set ] (N ∈ ℕbh x) × N ⊆ U ∥ → N ⊆ U
        helper' = {!!}

        N∈𝒰→N⊆U : (N : ℙ (X .set)) → N ∈ 𝒰 → N ⊆ U
        N∈𝒰→N⊆U _ p = helper' (∈→Inhab P p)

        𝕌⊆U : 𝕌 ⊆ U
        𝕌⊆U = union⊆ N∈𝒰→N⊆U

        helper'' : (x : X .set) → x ∈ U → Σ[ N ∈ ℙ (X .set) ] (N ∈ ℕbh x) × (N ⊆ U)
          → Σ[ N ∈ ℙ (X .set) ] (x ∈ N) × (N ∈ 𝒰)
        helper'' x x∈U (N , N∈Nx , N⊆U) = N , N∈ℕbhx→x∈N N∈Nx , Inhab→∈ P ∣ x , N∈Nx , N⊆U ∣

        helper''' : ∥ ((x : X .set) → x ∈ U → Σ[ N ∈ ℙ (X .set) ] (N ∈ ℕbh x) × (N ⊆ U)) ∥
          → (x : X .set) → x ∈ U → ∥ Σ[ N ∈ ℙ (X .set) ] (x ∈ N) × (N ∈ 𝒰) ∥
        helper''' = {!!}

        module _
          (p : ∥ ((x : X .set) → x ∈ U → Σ[ N ∈ ℙ (X .set) ] (N ∈ ℕbh x) × (N ⊆ U)) ∥) where

          U⊆𝕌 : U ⊆ 𝕌
          U⊆𝕌 x∈U = ∈union (helper''' p _ x∈U)

          𝕌≡U : 𝕌 ≡ U
          𝕌≡U = bi⊆→≡ 𝕌⊆U U⊆𝕌

          U∈Open : U ∈ X .openset
          U∈Open = subst (_∈ X .openset) 𝕌≡U 𝕌∈Open

    ℕbhCriterionOfOpenness : (U : ℙ (X .set)) → ((x : X .set) → x ∈ U → x ∈∘ U) → U ∈ X .openset
    ℕbhCriterionOfOpenness U p =
      U∈Open _ (choice2 (X .isset) (λ _ → isProp→isSet (isProp∈ {A = U})) (λ _ _ → isProp→isSet isProp∈∙) p)

    Thm : isHausdorff → (K : ℙ (X .set)) → isCompactSubset K → isClosed K
    Thm p K compt = {!!}
