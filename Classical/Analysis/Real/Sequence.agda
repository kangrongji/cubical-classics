{-

Sequence of Real Numbers

This file contains:
- Basic properties of real-number sequence;
- The notion of convergence and limit of sequences;
- The notion of Cauchy sequence;
- The monotone convergence theorem.

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
  using (<-weaken) renaming (_>_ to _>ℕ_ ; _<_ to _<ℕ_ ; _≥_ to _≥ℕ_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset
open import Classical.Preliminary.Nat
open import Classical.Algebra.OrderedRing.AbsoluteValue
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Extremum
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Analysis.Real.Base


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

  record Limit (seq : ℕ → ℝ) : Type where
    field
      lim : ℝ
      conv : isConvergentTo seq lim

  open Limit


  {-

    Monotone Convergence Theorem

  -}

  -- Monotone increasing and bounded sequence

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

  monotoneLim : {seq : ℕ → ℝ} → isIncreasing seq → isUpperBoundedSequence seq → Limit seq
  monotoneLim {seq = seq} incr boundSeq = record { lim = limit ; conv = λ ε ε>0 → ∣ n₀ ε ε>0 , ε-δ ε ε>0 ∣ }
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
      lim-ε<lim = +-rNeg→< (-Reverse>0 ε>0)

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

    Cauchy Sequence

  -}

  isCauchy : (ℕ → ℝ) → Type
  isCauchy seq = (ε : ℝ) → ε > 0 → ∥ Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → abs (seq m - seq n) < ε) ∥
