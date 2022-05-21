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
  using    (ℕ ; suc ; zero)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
  using    (<-weaken ; ≤0→≡0)
  renaming (_>_ to _>ℕ_ ; _<_ to _<ℕ_
          ; _≥_ to _≥ℕ_ ; _≤_ to _≤ℕ_
          ; isProp≤  to isProp≤ℕ
          ; ≤-refl   to ≤ℕ-refl
          ; <-trans  to <ℕ-trans
          ; <≤-trans to <≤ℕ-trans
          ; ≤<-trans to ≤<ℕ-trans)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
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


module Sequence (decide : LEM) where

  open Powerset  decide
  open Real      decide
  open OrderedFieldStr (ℝCompleteOrderedField .fst)
  open AbsoluteValue   (ℝCompleteOrderedField .fst .fst)
  open TopologyOfReal decide
  open MetricStr decide
  open Metric   ℝMetric


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

      ∣x-y∣<ε : abs (p .lim - q .lim) < ε
      ∣x-y∣<ε = Prop.rec2 isProp<
        (λ (n₀ , abs<₀) (n₁ , abs<₁) →
          let n = sucmax n₀ n₁ in
          ≤<-trans (dist-Δ _ _ _) (transport
            (λ i → abs (p .lim - seq n) + dist-symm (q .lim) (seq n) i < x/2+x/2≡x ε i)
            (+-Pres< (abs<₀ _ sucmax>left) (abs<₁ _ sucmax>right))))
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
  isClusteringAt seq x = (n₀ : ℕ)(ε : ℝ) → ε > 0 → ∥ Σ[ n ∈ ℕ ] (n₀ <ℕ n) × (abs (x - seq n) < ε) ∥

  isPropIsClusteringAt :  {seq : ℕ → ℝ}{x : ℝ} → isProp (isClusteringAt seq x)
  isPropIsClusteringAt = isPropΠ3 (λ _ _ _ → squash)

  record ClusterPoint (seq : ℕ → ℝ) : Type where
    field
      real : ℝ
      accum : isClusteringAt seq real

  open ClusterPoint


  -- A stronger version with more-than-mere-existence,
  -- but they turn out to be (logically) equivalent.

  isClusteringAtΣ : (ℕ → ℝ) → ℝ → Type
  isClusteringAtΣ seq x = (n₀ : ℕ)(ε : ℝ) → ε > 0 → Σ[ n ∈ ℕ ] (n₀ <ℕ n) × (abs (x - seq n) < ε)

  isClusteringAt→isClusteringAtΣ : {seq : ℕ → ℝ}{x : ℝ} → isClusteringAt seq x → isClusteringAtΣ seq x
  isClusteringAt→isClusteringAtΣ cluster n₀ ε ε>0 =
    find (λ _ → isProp× isProp≤ℕ isProp<) (λ _ → decide (isProp× isProp≤ℕ isProp<)) (cluster n₀ ε ε>0)


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
    ∃cluster n₀ ε ε>0 = Prop.rec2 squash
      (λ (m₀ , fin>x₀) (x , x₀-ε<x , x∈sub) →
      let m = sucmax n₀ m₀ in Prop.map
      (λ (n , n≥m , x≤seqn) →
        let x₀-ε<seqn : x₀ - ε < seq n
            x₀-ε<seqn = <≤-trans x₀-ε<x x≤seqn
            seqn<x₀+ε : seq n < x₀ + ε
            seqn<x₀+ε = fin>x₀ n (<-weaken (<≤ℕ-trans sucmax>right n≥m))
        in  n , <≤ℕ-trans sucmax>left n≥m ,
            absInOpenInterval ε>0 x₀-ε<seqn seqn<x₀+ε)
      (∈→Inhab accum-prop x∈sub m)) (∃fin>x₀ ε ε>0)
      (<sup→∃∈ _ accum-sup (-rPos→< ε>0))


  {-

    Cauchy Sequence

  -}

  -- We say a sequence is Cauchy,
  -- if for any ε > 0, there merely exists N ∈ ℕ
  -- such that whenever m n > N,
  -- the distance between the m-th and n-th terms is smaller than ε.
  -- In other words, the terms are crowding together when n approaching infinity.

  isCauchy : (ℕ → ℝ) → Type
  isCauchy seq = (ε : ℝ) → ε > 0 → ∥ Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → abs (seq m - seq n) < ε) ∥


  -- Cauchy sequence is bounded

  isCauchy→isBoundedSequence : {seq : ℕ → ℝ} → isCauchy seq → isBoundedSequence seq
  isCauchy→isBoundedSequence {seq = seq} cauchy = bSeq
    where

    finBound : (n : ℕ) → Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] ((m : ℕ) → (m ≤ℕ n) → (a ≤ seq m) × (seq m ≤ b))
    finBound zero = seq 0 , seq 0 , λ m m≤n →
      subst (λ k → (seq 0 ≤ seq k) × (seq k ≤ seq 0)) (sym (≤0→≡0 m≤n)) (≤-refl refl , ≤-refl refl)
    finBound (suc n) = a , b , λ m m≤n → case-split m (≤-ind m≤n)
      where
      a' = finBound n .fst
      b' = finBound n .snd .fst
      bfin = finBound n .snd .snd

      a = min a' (seq (suc n))
      b = max b' (seq (suc n))

      case-split : (m : ℕ) → (m ≤ℕ n) ⊎ (m ≡ suc n) → (a ≤ seq m) × (seq m ≤ b)
      case-split m (inl m≤n) = ≤-trans min≤left (bfin _ m≤n .fst) , ≤-trans (bfin _ m≤n .snd) max≥left
      case-split m (inr m≡sn) = subst (λ k → (a ≤ seq k) × (seq k ≤ b)) (sym m≡sn) (min≤right , max≥right)

    module _
      (ε : ℝ)(ε>0 : ε > 0)(n₀ : ℕ)
      (abs< : (n : ℕ) → n >ℕ n₀ → abs (seq n₀ - seq n) < ε) where

      a = finBound n₀ .fst
      b = finBound n₀ .snd .fst
      bfin = finBound n₀ .snd .snd

      case-split : (n : ℕ) → (n >ℕ n₀) ⊎ (n ≤ℕ n₀) → (a - ε ≤ seq n) × (seq n ≤ b + ε)
      case-split n (inr n≤n₀) =
        ≤-trans (inl (-rPos→< ε>0)) (bfin _ n≤n₀ .fst) ,
        ≤-trans (bfin _ n≤n₀ .snd) (inl (+-rPos→> ε>0))
      case-split n (inl n>n₀) =
        inl (absSuppress≥ (bfin _ ≤ℕ-refl .fst) (abs< _ n>n₀)) ,
        inl (absSuppress≤ (bfin _ ≤ℕ-refl .snd) (abs< _ n>n₀))

      ΣbSeq : Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] ((n : ℕ) → (a ≤ seq n) × (seq n ≤ b))
      ΣbSeq = a - ε , b + ε , λ n → case-split n (<≤-split n₀ n)

    bSeq : isBoundedSequence seq
    bSeq = Prop.map
      (λ (n₀ , abs<') → ΣbSeq 1 1>0 (suc n₀)
        (λ n n>sn₀ →
          abs<' (suc n₀) n ≤ℕ-refl (<ℕ-trans ≤ℕ-refl n>sn₀)))
      (cauchy 1 1>0)


  -- Real Number is Cauchy Complete

  isCauchy→Limit : {seq : ℕ → ℝ} → isCauchy seq → Limit seq
  isCauchy→Limit {seq = seq} cauchy = record { lim = cluster .real ; conv = convergent }
    where

    cluster = isBounded→ClusterPoint (isCauchy→isBoundedSequence cauchy)

    module _ (ε : ℝ)(ε>0 : ε > 0) where

      ε/2 = middle 0 ε
      ε/2>0 = middle>l ε>0

      convergent : ∥ Σ[ n₀ ∈ ℕ ] ((n : ℕ) → n >ℕ n₀ → abs (cluster .real - seq n) < ε) ∥
      convergent = Prop.rec squash
        (λ (n₀ , ∀abs<) → Prop.map
        (λ (n₁ , n₁>n₀ , abs<) →
          n₁ , λ n n>n₁ → subst (abs (cluster .real - seq n) <_) (x/2+x/2≡x ε)
            (≤<-trans (dist-Δ _ _ _) (+-Pres< abs< (∀abs< n₁ n n₁>n₀ (<ℕ-trans n₁>n₀ n>n₁)))))
        (cluster .accum n₀ ε/2 ε/2>0))
        (cauchy ε/2 ε/2>0)
