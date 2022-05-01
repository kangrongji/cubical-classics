{-

The Real Number

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Analysis.Real.Base.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.Rationals.QuoQ
open import Cubical.Relation.Nullary

open import Classical.Preliminary.Rational
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Analysis.Real.Base.DedekindCut
open import Classical.Analysis.Real.Base.AlgebraicStructure


module Order (decide : LEM) where

  open Powerset decide
  open Real     decide

  open DedekindCut
  open AlgebraicStructure decide

  {-

    Strict Ordering

  -}

  _<ℝ_ : ℝ → ℝ → Type
  a <ℝ b = a ≤ℝ b × ∥ Σ[ q ∈ ℚ ] ((r : ℚ) → r ∈ b .upper → q < r) × q ∈ a .upper ∥

  _>ℝ_ : ℝ → ℝ → Type
  a >ℝ b = b <ℝ a

  data Dichotomyℝ (a b : ℝ) : Type where
    ge : a ≥ℝ b → Dichotomyℝ a b
    lt : a <ℝ b → Dichotomyℝ a b

  dichotomyℝ : (a b : ℝ) → Dichotomyℝ a b
  dichotomyℝ = {!!}

  <ℝ-reverse : (a b : ℝ) → a <ℝ b → (-ℝ b) ≤ℝ (-ℝ a)
  <ℝ-reverse = {!!}


  -- Two lemmas for convenient case-splitting

  a≥0+-a≥0→a≡0 : {a : ℝ} → a ≥ℝ 0 → (-ℝ a) ≥ℝ 0 → a ≡ 0
  a≥0+-a≥0→a≡0 = {!!}

  a<0+-a<0→⊥ : {a : ℝ} → a <ℝ 0 → (-ℝ a) <ℝ 0 → ⊥
  a<0+-a<0→⊥ = {!!}


  {-

    Absolute Value

  -}

  -0≡0 : -ℝ 0 ≡ 0
  -0≡0 = sym (+ℝ-rUnit (-ℝ 0)) ∙ +ℝ-lInverse 0

  absℝ : ℝ → ℝ₊
  absℝ a with dichotomyℝ a 0
  ... | ge a≥0 = a , a≥0
  ... | lt a<0 = -ℝ a , subst (_≤ℝ (-ℝ a)) -0≡0 (<ℝ-reverse a 0 a<0)

  abs-ℝ : (a : ℝ) → absℝ (-ℝ a) ≡ absℝ a
  abs-ℝ a with dichotomyℝ a 0 | dichotomyℝ (-ℝ a) 0
  ... | ge a≥0 | ge -a≥0 = path-ℝ₊ _ _ (subst (λ x → -ℝ x ≡ x) (sym (a≥0+-a≥0→a≡0 a≥0 -a≥0)) -0≡0)
  ... | lt a<0 | lt -a<0 = Empty.rec (a<0+-a<0→⊥ {a = a} a<0 -a<0)
  ... | ge a≥0 | lt -a<0 = path-ℝ₊ _ _ (-ℝ-Involutive a)
  ... | lt a<0 | ge -a≥0 = path-ℝ₊ _ _ refl


  {-

    Multiplication

  -}

  _·ℝ_ : ℝ → ℝ → ℝ
  (a ·ℝ b) with dichotomyℝ a 0 | dichotomyℝ b 0
  ... | ge _ | ge _ = ((absℝ a) ·ℝ₊ (absℝ b)) .fst
  ... | lt _ | lt _ = ((absℝ a) ·ℝ₊ (absℝ b)) .fst
  ... | ge _ | lt _ = -ℝ (((absℝ a) ·ℝ₊ (absℝ b)) .fst)
  ... | lt _ | ge _ = -ℝ (((absℝ a) ·ℝ₊ (absℝ b)) .fst)

  ·ℝ-Comm : (a b : ℝ) → a ·ℝ b ≡ b ·ℝ a
  ·ℝ-Comm a b i with dichotomyℝ a 0 | dichotomyℝ b 0
  ... | ge _ | ge _ = ·ℝ₊-Comm (absℝ a) (absℝ b) i .fst
  ... | lt _ | lt _ = ·ℝ₊-Comm (absℝ a) (absℝ b) i .fst
  ... | ge _ | lt _ = -ℝ (·ℝ₊-Comm (absℝ a) (absℝ b) i .fst)
  ... | lt _ | ge _ = -ℝ (·ℝ₊-Comm (absℝ a) (absℝ b) i .fst)


  neg-·ℝ : (a b : ℝ) → ((-ℝ a) ·ℝ b) ≡ -ℝ (a ·ℝ b)
  neg-·ℝ a b = {!!} --with dichotomyℝ a 0 | dichotomyℝ b 0 | dichotomyℝ (-ℝ a) 0

  ·ℝ-neg : (a b : ℝ) → (a ·ℝ (-ℝ b)) ≡ -ℝ (a ·ℝ b)
  ·ℝ-neg a b = ·ℝ-Comm a (-ℝ b) ∙ neg-·ℝ b a ∙ cong (-ℝ_) (·ℝ-Comm b a)

  neg-·ℝ-neg : (a b : ℝ) → ((-ℝ a) ·ℝ (-ℝ b)) ≡ a ·ℝ b
  neg-·ℝ-neg a b = neg-·ℝ a (-ℝ b) ∙ cong (-ℝ_) (·ℝ-neg a b) ∙ -ℝ-Involutive (a ·ℝ b)


{-
  ·ℝ-Assoc : (a b c : ℝ) → a ·ℝ (b ·ℝ c) ≡ (a ·ℝ b) ·ℝ c
  ·ℝ-Assoc a b c i with dichotomyℝ a 0 | dichotomyℝ b 0 | dichotomyℝ c 0
  ... | ge _ | ge _ | ge _ = ·ℝ₊-Assoc (absℝ a) (absℝ b) (absℝ c) i .fst
  ... | ge _ | ge _ | lt _ = {!!}
  ... | lt _ | lt _ | ge _ = {!!}
  ... | lt _ | lt _ | lt _ = {!!}
  ... | ge _ | lt _ | ge _ = {!!}
  ... | ge _ | lt _ | lt _ = {!!}
  ... | lt _ | ge _ | ge _ = {!!}
  ... | lt _ | ge _ | lt _ = {!!}-}
