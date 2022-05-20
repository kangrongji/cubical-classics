{-

Sequence of Real Numbers

This file contains:
- Basic properties of real-number sequence;
- The notion of convergence and limit of sequences;
- The notion of Cauchy sequence;
- The notion of cluster points;
- The monotone convergence theorem;
- The Bolzano-Weierstrass theorem;
- The convergence of Cauchy sequences, or ℝ is Cauchy complete.

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
  using    (ℕ ; suc ; max)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
  using    (<-weaken ; left-≤-max ; right-≤-max)
  renaming (_>_ to _>ℕ_ ; _<_ to _<ℕ_
          ; _≥_ to _≥ℕ_ ; _≤_ to _≤ℕ_
          ; ≤-refl to ≤ℕ-refl
          ; ≤<-trans to ≤<ℕ-trans)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset
open import Classical.Preliminary.Nat
open import Classical.Preliminary.Logic
open import Classical.Algebra.OrderedRing.AbsoluteValue
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Extremum
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Topology.Metric
open import Classical.Analysis.Real.Base
open import Classical.Analysis.Real.Topology


module Cauchy (decide : LEM) where

  open Powerset decide
  open Real     decide
  open OrderedFieldStr (ℝCompleteOrderedField .fst)
  open AbsoluteValue   (ℝCompleteOrderedField .fst .fst)


  {-

    Convergence and Limit of Real Number Sequence

  -}

  isConvergentTo : (ℕ → ℝ) → ℝ → Type
  isConvergentTo seq x = (ε : ℝ) → ε > 0 → ∥ Σ[ n₀ ∈ ℕ ] ((n : ℕ) → n >ℕ n₀ → abs (x - seq n) < ε) ∥

  isPropIsConvergentTo : {seq : ℕ → ℝ}{x : ℝ} → isProp (isConvergentTo seq x)
  isPropIsConvergentTo = isPropΠ2 (λ _ _ → squash)

  record Limit (seq : ℕ → ℝ) : Type where
    field
      lim : ℝ
      conv : isConvergentTo seq lim

  open Limit

  -- The uniqueness of limit

  isPropLimit : {seq : ℕ → ℝ} → isProp (Limit seq)
  isPropLimit {seq = seq} p q i .conv =
    isProp→PathP (λ i → isPropIsConvergentTo {x = isPropLimit p q i .lim}) (p .conv) (q .conv) i
  isPropLimit {seq = seq} p q i .lim = infinitesimalDiff ∣x-y∣<ε i
    where

    module _ (ε : ℝ)(ε>0 : ε > 0) where

      ε/2 = middle 0 ε
      ε/2>0 = middle>l ε>0

      module _
        (n₀ : ℕ)(abs<₀ : (n : ℕ) → n >ℕ n₀ → abs (p .lim - seq n) < ε/2)
        (n₁ : ℕ)(abs<₁ : (n : ℕ) → n >ℕ n₁ → abs (q .lim - seq n) < ε/2) where

        n : ℕ
        n = suc (max n₀ n₁)

        n>n₀ : n >ℕ n₀
        n>n₀ = ≤<ℕ-trans left-≤-max ≤ℕ-refl

        n>n₁ : n >ℕ n₁
        n>n₁ = ≤<ℕ-trans right-≤-max ≤ℕ-refl

        open TopologyOfReal decide
        open MetricStr decide
        open Metric   ℝMetric

        abs< : abs (p .lim - q .lim) < ε
        abs< = ≤<-trans (dist-Δ _ _ _) (transport
          (λ i → abs (p .lim - seq n) + dist-symm (q .lim) (seq n) i < x/2+x/2≡x ε i)
          (+-Pres< (abs<₀ _ n>n₀) (abs<₁ _ n>n₁)))

      ∣x-y∣<ε : abs (p .lim - q .lim) < ε
      ∣x-y∣<ε = Prop.rec2 isProp<
        (λ (n₀ , abs<₀) (n₁ , abs<₁) → abs< n₀ abs<₀ n₁ abs<₁)
        (p .conv ε/2 ε/2>0) (q .conv ε/2 ε/2>0)


  {-

    Monotone Convergence Theorem

  -}

  -- Monotone increasing and upper-bounded sequence

  isIncreasing : (ℕ → ℝ) → Type
  isIncreasing seq = (n : ℕ) → seq (suc n) ≥ seq n

  isUpperBoundedSequence : (ℕ → ℝ) → Type
  isUpperBoundedSequence seq = ∥ Σ[ b ∈ ℝ ] ((n : ℕ) → seq n ≤ b) ∥


  open CompleteOrderedField decide
  open Completeness    (ℝCompleteOrderedField .fst)
  open Extremum decide (ℝCompleteOrderedField .fst)
  open Supremum

  private
    getSup = ℝCompleteOrderedField .snd


  -- Monotone increasing and upper-bounded sequence has a limit.

  isMonoBounded→Limit : {seq : ℕ → ℝ} → isIncreasing seq → isUpperBoundedSequence seq → Limit seq
  isMonoBounded→Limit {seq = seq} incr boundSeq = record { lim = limit ; conv = λ ε ε>0 → ∣ n₀ ε ε>0 , ε-δ ε ε>0 ∣ }
    where

    seq-prop : ℝ → hProp _
    seq-prop x = ∥ Σ[ n ∈ ℕ ] seq n ≡ x ∥ , squash

    seq-sub : ℙ ℝ
    seq-sub = specify seq-prop

    boundSub : isUpperBounded seq-sub
    boundSub = Prop.map
      (λ (b , seqn≤b) → b ,
        λ r r∈sub → Prop.rec isProp≤
        (λ (n , seqn≡r) →
          subst (_≤ b) seqn≡r (seqn≤b n))
        (∈→Inhab seq-prop r∈sub))
      boundSeq

    seq-sup : Supremum seq-sub
    seq-sup = getSup ∣ _ , Inhab→∈ seq-prop ∣ 0 , refl ∣ ∣ boundSub

    limit : ℝ
    limit = seq-sup .sup

    module _ (ε : ℝ)(ε>0 : ε > 0) where

      P : ℕ → Type
      P n = limit - seq n < ε

      lim-ε<lim : limit - ε < limit
      lim-ε<lim = -rPos→< ε>0

      ∃p : ∥ Σ[ n ∈ ℕ ] P n ∥
      ∃p = Prop.rec squash
        (λ (x , lim-ε<x , x∈sub) → Prop.map
          (λ (n , seqn≡x) →
            let lim-ε<seqn : limit - ε < seq n
                lim-ε<seqn = subst (limit - ε <_) (sym seqn≡x) lim-ε<x
                lim-seqn<ε : limit - seq n < ε
                lim-seqn<ε = +-MoveRToL<' (-MoveLToR< lim-ε<seqn)
            in  n , lim-seqn<ε)
          (∈→Inhab seq-prop x∈sub))
        (<sup→∃∈ _ seq-sup lim-ε<lim)

      Σp : Σ[ n ∈ ℕ ] limit - seq n < ε
      Σp = find (λ _ → isProp<) (λ _ → decide isProp<) ∃p

      n₀ = Σp .fst

      ε-δ' : (n k : ℕ) → k +ℕ n₀ ≡ n → limit - seq n < ε
      ε-δ' n 0 n₀≡n = subst (λ n → limit - seq n < ε) n₀≡n (Σp .snd)
      ε-δ' n (suc k) sk+n₀≡n = subst (λ n → limit - seq n < ε) sk+n₀≡n
        (≤<-trans (+-lPres≤ (-Reverse≤ (incr _))) (ε-δ' (k +ℕ n₀) k refl))

      lim-seqn≥0 : (n : ℕ) → limit - seq n ≥ 0
      lim-seqn≥0 n = ≥→Diff≥0 (seq-sup .bound _ (Inhab→∈ seq-prop ∣ _ , refl ∣))

      ε-δ : (n : ℕ) → n >ℕ n₀ → abs (limit - seq n) < ε
      ε-δ n n>n₀ = let (k , p) = <-weaken n>n₀ in
        subst (_< ε) (sym (x≥0→abs≡x (lim-seqn≥0 n))) (ε-δ' n k p)


  {-

    Cluster Points

  -}

  isClusteringAt : (ℕ → ℝ) → ℝ → Type
  isClusteringAt seq x = (ε : ℝ) → ε > 0 → ∥ Σ[ n ∈ ℕ ] abs (x - seq n) < ε ∥

  isPropIsClusteringAt :  {seq : ℕ → ℝ}{x : ℝ} → isProp (isClusteringAt seq x)
  isPropIsClusteringAt = isPropΠ2 (λ _ _ → squash)

  record ClusterPoint (seq : ℕ → ℝ) : Type where
    field
      real : ℝ
      accum : isClusteringAt seq real

  open ClusterPoint


  {-

    The Bolzano-Weierstrass Theorem

  -}

  -- Bounded sequence

  isBoundedSequence : (ℕ → ℝ) → Type
  isBoundedSequence seq = ∥ Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] ((n : ℕ) → (a ≤ seq n) × (seq n ≤ b)) ∥


  -- Sequence of real numbers admits cluster point when it is bounded.

  isBounded→ClusterPoint : {seq : ℕ → ℝ} → isBoundedSequence seq → ClusterPoint seq
  isBounded→ClusterPoint {seq = seq} bSeq = record { real = x₀ ; accum = ∃cluster }
    where

    accum-prop : ℝ → hProp _
    accum-prop x = ((n : ℕ) → ∥ Σ[ n' ∈ ℕ ] (n ≤ℕ n') × (x ≤ seq n') ∥) ,
      isPropΠ (λ _ → squash)

    accum-sub = specify accum-prop

    module _
      ((a , b , bound) : Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] ((n : ℕ) → (a ≤ seq n) × (seq n ≤ b)))
      where

      a∈accum : a ∈ accum-sub
      a∈accum = Inhab→∈ accum-prop (λ n → ∣ n , ≤ℕ-refl , bound n .fst ∣)

      x∈accum→x≤b : (x : ℝ) → x ∈ accum-sub → x ≤ b
      x∈accum→x≤b x x∈accum = ¬<→≥ ¬x>b
        where
        ¬x>b : ¬ x > b
        ¬x>b x>b = Prop.rec isProp⊥
          (λ (n , _ , x≤seqn) →
            <≤-asym x>b (≤-trans x≤seqn (bound n .snd)))
          (∈→Inhab accum-prop x∈accum 0)

      inhabSub : isInhabited  accum-sub
      inhabSub = ∣ a , a∈accum ∣

      boundSub : isUpperBounded  accum-sub
      boundSub = ∣ b , x∈accum→x≤b ∣

    accum-sup : Supremum accum-sub
    accum-sup = getSup (Prop.rec squash inhabSub bSeq) (Prop.rec squash boundSub bSeq)

    x₀ = accum-sup .sup

    open ClassicalLogic decide

    ∃fin>x₀ : (ε : ℝ) → ε > 0 → ∥ Σ[ n₀ ∈ ℕ ] ((n : ℕ) → n₀ ≤ℕ n → seq n < x₀ + ε) ∥
    ∃fin>x₀  ε ε>0 = Prop.map
      (λ (n₀ , ¬p) →
        n₀ , λ n n₀≤n → ¬≤→> (¬∃→∀¬2 ¬p n n₀≤n))
      (¬∀→∃¬ (λ _ → squash) (∉→Empty accum-prop
        (¬∈→∉ {A = accum-sub} (>sup→¬∈ _ accum-sup (+-rPos→> ε>0)))))

    ∃cluster : isClusteringAt seq x₀
    ∃cluster ε ε>0 = Prop.rec2 squash
      (λ (m , fin>x₀) (x , x₀-ε<x , x∈sub) → Prop.map
      (λ (n , n≥m , x≤seqn) →
        let x₀-ε<seqn : x₀ - ε < seq n
            x₀-ε<seqn = <≤-trans x₀-ε<x x≤seqn
            seqn<x₀+ε : seq n < x₀ + ε
            seqn<x₀+ε = fin>x₀ n n≥m
        in  n , absInOpenInterval ε>0 x₀-ε<seqn seqn<x₀+ε)
      (∈→Inhab accum-prop x∈sub m)) (∃fin>x₀ ε ε>0)
      (<sup→∃∈ _ accum-sup (-rPos→< ε>0))


  {-

    Cauchy Sequence

  -}

  -- We say a sequence is Cauchy,
  -- if for any ε > 0, there merely exists N ∈ ℕ
  -- such that whenever m n > N,
  -- the distance between the m-th and n-th terms is smaller than ε.
  -- In other words, the sequence is condensed when n approaching infinity.

  isCauchy : (ℕ → ℝ) → Type
  isCauchy seq = (ε : ℝ) → ε > 0 → ∥ Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → abs (seq m - seq n) < ε) ∥


  -- Cauchy sequence is bounded

  isCauchy→isBoundedSequence : {seq : ℕ → ℝ} → isCauchy seq → isBoundedSequence seq
  isCauchy→isBoundedSequence = {!!}


  -- Real Number is Cauchy Complete

  isCauchy→Limit : {seq : ℕ → ℝ} → isCauchy seq → Limit seq
  isCauchy→Limit {seq = seq} cauchy = {!!}
