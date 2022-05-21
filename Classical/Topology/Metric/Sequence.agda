{-

Sequence in Metric Space

This file contains:
- Basics of sequence (of points) in metric space;
- The notion of convergence and limit of sequences;
- The notion of cluster points;
- The notion of Cauchy sequence;
- The notion of Cauchy completeness.

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Metric.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using ()
  renaming (_>_ to _>ℕ_ ; _<_ to _<ℕ_
          ; _≥_ to _≥ℕ_ ; _≤_ to _≤ℕ_
          ; isProp≤  to isProp≤ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms
open import Classical.Foundations.Powerset
open import Classical.Preliminary.Nat
open import Classical.Algebra.OrderedField
open import Classical.Topology.Metric
open import Classical.Analysis.Real.Base

private
  variable
    ℓ : Level


module _ ⦃ 🤖 : Oracle ⦄
  {X : Type ℓ} ⦃ 𝓂 : Metric X ⦄ where

  open Oracle 🤖

  open OrderedFieldStr (ℝCompleteOrderedField .fst)
  open Metric 𝓂


  {-

    Convergence and Limit of Real Number Sequence

  -}

  isConvergentTo : (ℕ → X) → X → Type
  isConvergentTo seq x = (ε : ℝ) → ε > 0 → ∥ Σ[ n₀ ∈ ℕ ] ((n : ℕ) → n >ℕ n₀ → 𝓂 .dist x (seq n) < ε) ∥

  isPropIsConvergentTo : {seq : ℕ → X}{x : X} → isProp (isConvergentTo seq x)
  isPropIsConvergentTo = isPropΠ2 (λ _ _ → squash)

  record Limit (seq : ℕ → X) : Type ℓ where
    field
      lim : X
      conv : isConvergentTo seq lim

  open Limit


  -- A stronger version with more-than-mere-existence,
  -- but they turn out to be (logically) equivalent.

  isConvergentToΣ : (ℕ → X) → X → Type
  isConvergentToΣ seq x = (ε : ℝ) → ε > 0 → Σ[ n₀ ∈ ℕ ] ((n : ℕ) → n >ℕ n₀ → 𝓂 .dist x (seq n) < ε)

  isConvergentTo→isConvergentToΣ : {seq : ℕ → X}{x : X} → isConvergentTo seq x → isConvergentToΣ seq x
  isConvergentTo→isConvergentToΣ converge ε ε>0 = findByOracle (λ _ → isPropΠ2 (λ _ _ → isProp<)) (converge ε ε>0)


  -- The uniqueness of limit

  isPropLimit : {seq : ℕ → X} → isProp (Limit seq)
  isPropLimit {seq = seq} p q i .conv =
    isProp→PathP (λ i → isPropIsConvergentTo {x = isPropLimit p q i .lim}) (p .conv) (q .conv) i
  isPropLimit {seq = seq} p q i .lim = infiClose ∣x-y∣<ε i
    where

    module _ (ε : ℝ)(ε>0 : ε > 0) where

      ε/2 = middle 0 ε
      ε/2>0 = middle>l ε>0

      ∣x-y∣<ε : 𝓂 .dist (p .lim) (q .lim) < ε
      ∣x-y∣<ε = Prop.rec2 isProp<
        (λ (n₀ , abs<₀) (n₁ , abs<₁) →
          let n = sucmax n₀ n₁ in
          ≤<-trans (dist-Δ _ _ _) (transport
            (λ i → 𝓂 .dist (p .lim) (seq n) + dist-symm (q .lim) (seq n) i < x/2+x/2≡x ε i)
            (+-Pres< (abs<₀ _ sucmax>left) (abs<₁ _ sucmax>right))))
        (p .conv ε/2 ε/2>0) (q .conv ε/2 ε/2>0)


  {-

    Cluster Points

  -}

  isClusteringAt : (ℕ → X) → X → Type
  isClusteringAt seq x = (n₀ : ℕ)(ε : ℝ) → ε > 0 → ∥ Σ[ n ∈ ℕ ] (n₀ <ℕ n) × (𝓂 .dist x (seq n) < ε) ∥

  isPropIsClusteringAt :  {seq : ℕ → X}{x : X} → isProp (isClusteringAt seq x)
  isPropIsClusteringAt = isPropΠ3 (λ _ _ _ → squash)

  record ClusterPoint (seq : ℕ → X) : Type ℓ where
    field
      point : X
      accum : isClusteringAt seq point

  open ClusterPoint


  -- A stronger version with more-than-mere-existence,
  -- but they turn out to be (logically) equivalent.

  isClusteringAtΣ : (ℕ → X) → X → Type
  isClusteringAtΣ seq x = (n₀ : ℕ)(ε : ℝ) → ε > 0 → Σ[ n ∈ ℕ ] (n₀ <ℕ n) × (𝓂 .dist x (seq n) < ε)

  isClusteringAt→isClusteringAtΣ : {seq : ℕ → X}{x : X} → isClusteringAt seq x → isClusteringAtΣ seq x
  isClusteringAt→isClusteringAtΣ cluster n₀ ε ε>0 = findByOracle (λ _ → isProp× isProp≤ℕ isProp<) (cluster n₀ ε ε>0)


  {-

    Cauchy Sequence

  -}

  -- We say a sequence is Cauchy,
  -- if for any ε > 0, there merely exists N ∈ ℕ
  -- such that whenever m n > N,
  -- the distance between the m-th and n-th terms is smaller than ε.
  -- In other words, the terms are crowding together when n approaching infinity.

  isCauchy : (ℕ → X) → Type
  isCauchy seq = (ε : ℝ) → ε > 0 → ∥ Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → 𝓂 .dist (seq m) (seq n) < ε) ∥


  -- A stronger version with more-than-mere-existence,
  -- but they turn out to be (logically) equivalent.

  isCauchyΣ : (ℕ → X) → Type
  isCauchyΣ seq = (ε : ℝ) → ε > 0 → Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → 𝓂 .dist (seq m) (seq n) < ε)

  isCauchy→isCauchyΣ : {seq : ℕ → X}{x : X} → isCauchy seq → isCauchyΣ seq
  isCauchy→isCauchyΣ cauchy ε ε>0 = findByOracle (λ _ → isPropΠ4 (λ _ _ _ _ → isProp<)) (cauchy ε ε>0)


  -- A metric space is Cauchy complete if every Cauchy sequence has a limit.

  isCauchyComplete : Type ℓ
  isCauchyComplete = {seq : ℕ → X} → isCauchy seq → Limit seq
