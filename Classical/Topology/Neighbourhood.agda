{-

Neighbourhood

This file contains:
- Basic properties of neighbourhood;
- Basic criterion for open/closed subset;
- Lemmas about separation by open subsets.

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Neighbourhood where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms
open import Classical.Foundations.Powerset

open import Classical.Topology.Base
open import Classical.Topology.Properties

private
  variable
    ℓ : Level


module _ ⦃ 🤖 : Oracle ⦄ where

  open Topology


  module _ {X : Type ℓ} ⦃ 𝒯 : Topology X ⦄ where

    {-

      Basics

    -}

    -- Neighbourhood around a given point

    ℕbh : X → ℙ ℙ X
    ℕbh x = rep x ∩ Open

    N∈ℕbhx→x∈N : {x : X}{N : ℙ X} → N ∈ ℕbh x → x ∈ N
    N∈ℕbhx→x∈N {x = x} N∈ℕx = left∈-∩ (rep x) Open N∈ℕx

    N∈ℕbhx→N∈Open : {x : X}{N : ℙ X} → N ∈ ℕbh x → N ∈ Open
    N∈ℕbhx→N∈Open {x = x} = right∈-∩ (rep x) Open

    makeℕbh : {x : X}{N : ℙ X} → x ∈ N → N ∈ Open → N ∈ ℕbh x
    makeℕbh {x = x} {N = N} x∈N N∈Open = ∈→∈∩ (rep x) Open x∈N N∈Open

    total∈ℕbh : {x : X} → total ∈ ℕbh x
    total∈ℕbh {x = x} = makeℕbh {x = x} (x∈total {x = x}) (𝒯 .has-total)

    ℕbh∩ : {x : X}{U V : ℙ X} → U ∈ ℕbh x → V ∈ ℕbh x → U ∩ V ∈ ℕbh x
    ℕbh∩ {U = U} {V = V} U∈ℕx V∈ℕx =
      makeℕbh (∩-∈rep U V (N∈ℕbhx→x∈N U∈ℕx) (N∈ℕbhx→x∈N V∈ℕx))
        (𝒯 .∩-close (N∈ℕbhx→N∈Open U∈ℕx) (N∈ℕbhx→N∈Open V∈ℕx))


    {-

      Interior of Subset

    -}


    -- Inside interior of some someset

    _Σ∈∘_ : (x : X) → (U : ℙ X) → Type _
    x Σ∈∘ U = Σ[ N ∈ ℙ X ] (N ∈ ℕbh x) × N ⊆ U


    -- It reads "the point x is inside the interior of U"
    -- or "x is an interior point of U".

    _∈∘_ : (x : X) → (U : ℙ X) → Type _
    x ∈∘ U = ∥ x Σ∈∘ U ∥

    ∈→∈∘ : {x : X}{U : ℙ X} → U ∈ Open → x ∈ U → x ∈∘ U
    ∈→∈∘ {U = U} U∈Open x∈U = ∣ _ , makeℕbh x∈U U∈Open , ⊆-refl {A = U} ∣


    -- A subset U is open,
    -- if every point x ∈ U merely has a neighberhood contained in U,

    ℕbhCriterionOfOpenness : {U : ℙ X} → ((x : X) → x ∈ U → x ∈∘ U) → U ∈ Open
    ℕbhCriterionOfOpenness {U = U} p = U∈Open
      where
      P : ℙ X → hProp _
      P N = ∥ Σ[ x ∈ X ] (N ∈ ℕbh x) × N ⊆ U ∥ , squash

      𝒰 : ℙ ℙ X
      𝒰 = specify P

      rec-helper1 : {N : ℙ X} → ∥ Σ[ x ∈ X ] (N ∈ ℕbh x) × N ⊆ U ∥ → N ∈ Open
      rec-helper1 = Prop.rec (isProp∈ Open) λ (_ , p , _) → N∈ℕbhx→N∈Open p

      𝒰⊆Open : 𝒰 ⊆ Open
      𝒰⊆Open p = rec-helper1 (∈→Inhab P p)

      𝕌 : ℙ X
      𝕌 = union 𝒰

      𝕌∈Open : 𝕌 ∈ Open
      𝕌∈Open = 𝒯 .∪-close 𝒰⊆Open

      rec-helper2 : {N : ℙ X} → ∥ Σ[ x ∈ X ] (N ∈ ℕbh x) × N ⊆ U ∥ → N ⊆ U
      rec-helper2 = Prop.rec isProp⊆ λ (_ , _ , p) → p

      N∈𝒰→N⊆U : (N : ℙ X) → N ∈ 𝒰 → N ⊆ U
      N∈𝒰→N⊆U _ p = rec-helper2 (∈→Inhab P p)

      𝕌⊆U : 𝕌 ⊆ U
      𝕌⊆U = union⊆ N∈𝒰→N⊆U

      U⊆𝕌 : U ⊆ 𝕌
      U⊆𝕌 x∈U = ∃→∈union
        (Prop.map (λ (N , N∈ℕx , N⊆U) → N , N∈ℕbhx→x∈N N∈ℕx , Inhab→∈ P ∣ _ , N∈ℕx , N⊆U ∣) (p _ x∈U))

      𝕌≡U : 𝕌 ≡ U
      𝕌≡U = bi⊆→≡ 𝕌⊆U U⊆𝕌

      U∈Open : U ∈ Open
      U∈Open = subst (_∈ Open) 𝕌≡U 𝕌∈Open


    {-

      Separation by Open Subsets

    -}

    -- Separating a point from a subset using open sets

    ΣSep : (x : X) → ℙ X → Type _
    ΣSep x A = Σ[ U ∈ ℙ X ] (U ∈ ℕbh x) × (A ∩ U ≡ ∅)

    ΣSep⊆ : {x : X}{A B : ℙ X} → A ⊆ B → ΣSep x B → ΣSep x A
    ΣSep⊆ {A = A} {B = B} A⊆B (U , U∈ℕx , B∩U≡∅) = U , U∈ℕx , A⊆B+B∩C≡∅→A∩C≡∅ A⊆B B∩U≡∅


    -- It reads as "there merely exists a neighbourhood of x that is separated from A".

    Sep : (x : X) → ℙ X → Type _
    Sep x A = ∥ ΣSep x A ∥

    Sep⊆ : {x : X}{A B : ℙ X} → A ⊆ B → Sep x B → Sep x A
    Sep⊆ A⊆B = Prop.map (ΣSep⊆ A⊆B)

    Sep→∈∘∁ : {x : X}{A : ℙ X} → Sep x A → x ∈∘ (∁ A)
    Sep→∈∘∁ = Prop.map (λ (U , U∈ℕx , A∩U≡∅) → U , U∈ℕx , A∩B=∅→A⊆∁B (∩-Comm _ _ ∙ A∩U≡∅))


    -- It reads as "there merely exists neighbourhood of x and A respectively that don't intersect with each other",
    -- or "point x and subset A are separating by open sets"

    SepOpen : (x : X) → ℙ X → Type _
    SepOpen x A = ∥ Σ[ U ∈ ℙ X ] Σ[ V ∈ ℙ X ] (U ∈ Open) × A ⊆ U × (V ∈ ℕbh x) × (A ∩ V ≡ ∅) ∥

    SepOpen⊆ : {x : X}{A U : ℙ X} → U ∈ Open → A ⊆ U → Sep x U → SepOpen x A
    SepOpen⊆ {U = U} U∈Open A⊆U =
      Prop.map (λ (V , V∈ℕx , U∩V≡∅) → U , V , U∈Open , A⊆U , V∈ℕx , A⊆B+B∩C≡∅→A∩C≡∅ A⊆U U∩V≡∅)

    SepOpen→Sep : {x : X}{A : ℙ X} → SepOpen x A → Sep x A
    SepOpen→Sep = Prop.map (λ (_ , V , _ , _ , V∈ℕx , A∩V≡∅) → V , V∈ℕx , A∩V≡∅)


    -- A subset K ⊆ X is closed if for any x ∉ K, there merely exists neigubourhood of x separating from K.

    SepCriterionOfClosedness : {K : ℙ X} → ((x : X) → x ∉ K → Sep x K) → K ∈ Closed
    SepCriterionOfClosedness {K = K} sep = ℕbhCriterionOfOpenness x∉K→x∈∘∁K
      where
      x∉K→x∈∘∁K : (x : X) → x ∈ (∁ K) → x ∈∘ (∁ K)
      x∉K→x∈∘∁K x x∈∁K = Sep→∈∘∁ (sep x (∈∁→∉ {A = K} x∈∁K))


    -- Given a finite covering 𝒰 such that,
    -- for any open U ∈ 𝒰, there merely exists a neighbourhood of x outside U,
    -- then there merely exists a neighbourhood of x that does not intersect with the union of opens in 𝒰.

    unionSep : (x : X)
      (𝒰 : ℙ ℙ X)(𝒰⊆Open : 𝒰 ⊆ Open)
      (sep : (U : ℙ X) → U ∈ 𝒰 → Sep x U)
      → isFinSub 𝒰 → Sep x (union 𝒰)
    unionSep _ _ 𝒰⊆Open sep (fin-squash p q i) = squash (unionSep _ _ 𝒰⊆Open sep p) (unionSep _ _ 𝒰⊆Open sep q) i
    unionSep x 𝒰 _ _ isfin∅ = ∣ total , total∈ℕbh {x = x} , ∩-rUnit (union 𝒰) ∙ union∅ ∣
    unionSep x 𝒰 𝒰⊆Open sep (isfinsuc {A = 𝒰₀} fin𝒰₀ U) = subst (Sep x) (sym union∪[A]) sep𝕌₀∪U
      where
      𝕌₀ : ℙ X
      𝕌₀ = union 𝒰₀

      𝒰₀⊆𝒰 : 𝒰₀ ⊆ 𝒰
      𝒰₀⊆𝒰 = ∪-left⊆ 𝒰₀ [ U ]

      𝒰₀⊆Open : 𝒰₀ ⊆ Open
      𝒰₀⊆Open = ⊆-trans {A = 𝒰₀} 𝒰₀⊆𝒰 𝒰⊆Open

      𝕌₀∈Open : 𝕌₀ ∈ Open
      𝕌₀∈Open = union∈Open 𝒰₀⊆Open

      -- TODO : Make a solver to deal with these problems.
      ∪∅-helper : {A B C D : ℙ X} → A ∩ C ≡ ∅ → B ∩ D ≡ ∅ → (A ∪ B) ∩ (C ∩ D) ≡ ∅
      ∪∅-helper {A = A} {B = B} {C = C} {D = D} A∩C≡∅ B∩D≡∅ =
          ∩-∪-lDist _ _ _
        ∙ (λ i → ∩-Assoc A C D i ∪ (B ∩ ∩-Comm C D i))
        ∙ (λ i → ((A ∩ C) ∩ D) ∪ ∩-Assoc B D C i)
        ∙ (λ i → (A∩C≡∅ i ∩ D) ∪ (B∩D≡∅ i ∩ C))
        ∙ (λ i → ∩-lZero D i ∪ ∩-lZero C i)
        ∙ ∪-Idem _

      ind-Sep-helper : (A B : ℙ X) → A ∈ Open → B ∈ Open → ΣSep x A → ΣSep x B → ΣSep x (A ∪ B)
      ind-Sep-helper _ _ _ _ (VA , VA∈Nx , VA∅) (VB , VB∈Nx , VB∅) =
        VA ∩ VB , ℕbh∩ VA∈Nx VB∈Nx , ∪∅-helper VA∅ VB∅

      ind-Sep : (A B : ℙ X) → A ∈ Open → B ∈ Open → _
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
