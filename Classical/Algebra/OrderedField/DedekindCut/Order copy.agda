{-

Order Structure on Dedekind Cuts

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Algebra.OrderedField.DedekindCut.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset
open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField

open import Classical.Algebra.OrderedField.DedekindCut.Base
open import Classical.Algebra.OrderedField.DedekindCut.Algebra

private
  variable
    ℓ ℓ' : Level


module Order (decide : LEM)
  (𝒦 : OrderedField ℓ ℓ')(archimedesK : isArchimedean (𝒦 . fst))
  where

  private
    K = 𝒦 .fst .fst .fst

  open Powerset decide

  open OrderedFieldStr 𝒦
  open Basics   decide 𝒦
  open Algebra  decide 𝒦 archimedesK
  open DedekindCut

  --open Helpers (𝒦 .fst .fst)

  {-

    Strict Ordering

  -}

  _<𝕂_ : 𝕂 → 𝕂 → Type (ℓ-max ℓ ℓ')
  a <𝕂 b = a ≤𝕂 b × ∥ Σ[ q ∈ K ] ((r : K) → r ∈ b .upper → q < r) × q ∈ a .upper ∥

  _>𝕂_ : 𝕂 → 𝕂 → Type (ℓ-max ℓ ℓ')
  a >𝕂 b = b <𝕂 a


  -- Strictness

  <𝕂→≤𝕂 : {a b : 𝕂} → a <𝕂 b → a ≤𝕂 b
  <𝕂→≤𝕂 = {!!}

  <𝕂→arefl : {a b : 𝕂} → a <𝕂 b → a ≡ b → ⊥
  <𝕂→arefl = {!!}

  ≤𝕂+≢→<𝕂 : {a b : 𝕂} → a ≤𝕂 b → ¬ a ≡ b → a <𝕂 b
  ≤𝕂+≢→<𝕂 = {!!}


  -- Properties

  data Dichotomy𝕂 (a b : 𝕂) : Type (ℓ-max ℓ ℓ') where
    ge : a ≥𝕂 b → Dichotomy𝕂 a b
    lt : a <𝕂 b → Dichotomy𝕂 a b

  dichotomy𝕂 : (a b : 𝕂) → Dichotomy𝕂 a b
  dichotomy𝕂 = {!!}

  <𝕂-reverse : (a b : 𝕂) → a <𝕂 b → (-𝕂 b) ≤𝕂 (-𝕂 a)
  <𝕂-reverse = {!!}

  <≤𝕂-asym : (a b : 𝕂) → a <𝕂 b → b ≥𝕂 a → ⊥
  <≤𝕂-asym = {!!}

  -- Two lemmas for convenient case-splitting

  a≥0+-a≥0→a≡0 : {a : 𝕂} → a ≥𝕂 𝟘 → (-𝕂 a) ≥𝕂 𝟘 → a ≡ 𝟘
  a≥0+-a≥0→a≡0 = {!!}

  a<0+-a<0→⊥ : {a : 𝕂} → a <𝕂 𝟘 → (-𝕂 a) <𝕂 𝟘 → ⊥
  a<0+-a<0→⊥ = {!!}


  {-

    Absolute Value

  -}

  -0≡0 : -𝕂 𝟘 ≡ 𝟘
  -0≡0 = sym (+𝕂-rUnit (-𝕂 𝟘)) ∙ +𝕂-lInverse 𝟘
{-
  abs𝕂 : 𝕂 → 𝕂
  abs𝕂 a with dichotomy𝕂 a 𝟘
  ... | ge a≥0 = a
  ... | lt a<0 = -𝕂 a

  --abs-Idem : (a : 𝕂) : 

  abs≥0 : (a : 𝕂) → abs𝕂 a ≥𝕂 𝟘
  abs≥0 a with dichotomy𝕂 a 𝟘
  ... | ge a≥0 = a≥0
  ... | lt a<0 = subst (_≤𝕂 (-𝕂 a)) -0≡0 (<𝕂-reverse a 𝟘 a<0)

  abs𝕂₊ : 𝕂 → 𝕂₊
  abs𝕂₊ a = abs𝕂 a , abs≥0 a

  abs-𝕂 : (a : 𝕂) → abs𝕂 (-𝕂 a) ≡ abs𝕂 a
  abs-𝕂 a with dichotomy𝕂 a 𝟘 | dichotomy𝕂 (-𝕂 a) 𝟘
  ... | ge a≥0 | ge -a≥0 = (subst (λ x → -𝕂 x ≡ x) (sym (a≥0+-a≥0→a≡0 a≥0 -a≥0)) -0≡0)
  ... | lt a<0 | lt -a<0 = Empty.rec (a<0+-a<0→⊥ {a = a} a<0 -a<0)
  ... | ge a≥0 | lt -a<0 = (-𝕂-Involutive a)
  ... | lt a<0 | ge -a≥0 = refl
-}

  abs𝕂 : 𝕂 → 𝕂₊
  abs𝕂 a with dichotomy𝕂 a 𝟘
  ... | ge a≥0 = a , a≥0
  ... | lt a<0 = -𝕂 a , subst (_≤𝕂 (-𝕂 a)) -0≡0 (<𝕂-reverse a 𝟘 a<0)

  abs-𝕂 : (a : 𝕂) → abs𝕂 (-𝕂 a) ≡ abs𝕂 a
  abs-𝕂 a with dichotomy𝕂 a 𝟘 | dichotomy𝕂 (-𝕂 a) 𝟘
  ... | ge a≥0 | ge -a≥0 = path-𝕂₊ _ _ (subst (λ x → -𝕂 x ≡ x) (sym (a≥0+-a≥0→a≡0 a≥0 -a≥0)) -0≡0)
  ... | lt a<0 | lt -a<0 = Empty.rec (a<0+-a<0→⊥ {a = a} a<0 -a<0)
  ... | ge a≥0 | lt -a<0 = path-𝕂₊ _ _ (-𝕂-Involutive a)
  ... | lt a<0 | ge -a≥0 = path-𝕂₊ _ _ refl


  {-

    Sign

  -}

{-
  Sign : Type
  Sign = Bool

  pattern pos = false
  pattern neg = true

  _·s_ : Sign → Sign → Sign
  _·s_ = _⊕_

  sign : 𝕂 → Sign
  sign a with dichotomy𝕂 a 𝟘
  ... | ge a≥0 = pos
  ... | lt a<0 = neg

  abs-sign-path : (a b : 𝕂) → abs𝕂 a ≡ abs𝕂 b → sign a ≡ sign b → a ≡ b
  abs-sign-path a b abs≡ sign≡ with dichotomy𝕂 a 𝟘 | dichotomy𝕂 b 𝟘
  ... | ge a≥0 | ge b≥0 = λ i → abs≡ i
  ... | lt a<0 | lt b<0 = sym (-𝕂-Involutive a) ∙ (λ i → -𝕂 (abs≡ i)) ∙ -𝕂-Involutive b
  ... | ge a≥0 | lt b<0 = Empty.rec (false≢true sign≡)
  ... | lt a<0 | ge b≥0 = Empty.rec (true≢false sign≡)-}

{-
  abs-sign-path : (a b : 𝕂) → abs𝕂 a ≡ abs𝕂 b → sign a ≡ sign b → a ≡ b
  abs-sign-path a b abs≡ sign≡ with dichotomy𝕂 a 𝟘 | dichotomy𝕂 b 𝟘
  ... | ge a≥0 | ge b≥0 = λ i → abs≡ i .fst
  ... | lt a<0 | lt b<0 = sym (-𝕂-Involutive a) ∙ (λ i → -𝕂 (abs≡ i .fst)) ∙ -𝕂-Involutive b
  ... | ge a≥0 | lt b<0 = Empty.rec (false≢true sign≡)
  ... | lt a<0 | ge b≥0 = Empty.rec (true≢false sign≡) -+ -}


  {-

    Multiplication

  -}

  _·𝕂_ : 𝕂 → 𝕂 → 𝕂
  (a ·𝕂 b) with dichotomy𝕂 a 𝟘 | dichotomy𝕂 b 𝟘
  ... | ge _ | ge _ = ((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) .fst
  ... | lt _ | lt _ = ((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) .fst
  ... | ge _ | lt _ = -𝕂 (((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) .fst)
  ... | lt _ | ge _ = -𝕂 (((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) .fst)
{-
  ·𝕂-abs : (a b : 𝕂) → abs𝕂 (a ·𝕂 b) ≡ (abs𝕂 a) ·𝕂 (abs𝕂 b)
  ·𝕂-abs a b with dichotomy𝕂 a 𝟘 | dichotomy𝕂 b 𝟘
  ... | ge _ | ge _ = refl
  ... | lt _ | lt _ = refl
  ... | ge _ | lt _ = {!!}
  ... | lt _ | ge _ = {!!}

  ·𝕂-sign : (a b : 𝕂) → sign (a ·𝕂 b) ≡ sign a ·s sign b
  ·𝕂-sign = {!!}-}

  ·𝕂-Comm : (a b : 𝕂) → a ·𝕂 b ≡ b ·𝕂 a
  ·𝕂-Comm a b i with dichotomy𝕂 a 𝟘 | dichotomy𝕂 b 𝟘
  ... | ge _ | ge _ = ·𝕂₊-Comm (abs𝕂 a) (abs𝕂 b) i .fst
  ... | lt _ | lt _ = ·𝕂₊-Comm (abs𝕂 a) (abs𝕂 b) i .fst
  ... | ge _ | lt _ = -𝕂 (·𝕂₊-Comm (abs𝕂 a) (abs𝕂 b) i .fst)
  ... | lt _ | ge _ = -𝕂 (·𝕂₊-Comm (abs𝕂 a) (abs𝕂 b) i .fst)

  ·𝕂-rZero : (a : 𝕂) → a ·𝕂 𝟘 ≡ 𝟘
  ·𝕂-rZero a with dichotomy𝕂 a 𝟘 | dichotomy𝕂 𝟘 𝟘
  ... | ge _ | ge _ = {!!}
  ... | lt _ | lt _ = {!!}
  ... | ge _ | lt _ = {!!}
  ... | lt _ | ge _ = {!!}

  ·𝕂-lZero : (a : 𝕂) → 𝟘 ·𝕂 a ≡ 𝟘
  ·𝕂-lZero a with dichotomy𝕂 a 𝟘 | dichotomy𝕂 𝟘 𝟘
  ... | ge _ | ge _ = {!!}
  ... | lt _ | lt _ = {!!}
  ... | ge _ | lt _ = {!!}
  ... | lt _ | ge _ = {!!}


  <0-explode : {a : 𝕂} → a <𝕂 𝟘 → (-𝕂 a) <𝕂 𝟘 → ⊥
  <0-explode = {!!}

  ≥0→≡0 : {a : 𝕂} → a ≥𝕂 𝟘 → (-𝕂 a) ≥𝕂 𝟘 → a ≡ 𝟘
  ≥0→≡0 = {!!}


  neg-·𝕂 : (a b : 𝕂) → ((-𝕂 a) ·𝕂 b) ≡ -𝕂 (a ·𝕂 b)
  neg-·𝕂 a b with dichotomy𝕂 a 𝟘 | dichotomy𝕂 (-𝕂 a) 𝟘 | dichotomy𝕂 b 𝟘
  ... | ge _ | lt _ | ge _ = λ i → -𝕂 ((abs-𝕂 a i) ·𝕂₊ (abs𝕂 b)) .fst
  ... | ge _ | lt _ | lt _ = λ i → -𝕂-Involutive (((abs-𝕂 a i) ·𝕂₊ (abs𝕂 b)) .fst) (~ i)
  ... | lt _ | ge _ | ge _ = λ i → -𝕂-Involutive (((abs-𝕂 a i) ·𝕂₊ (abs𝕂 b)) .fst) (~ i)
  ... | lt _ | ge _ | lt _ = λ i → -𝕂 ((abs-𝕂 a i) ·𝕂₊ (abs𝕂 b)) .fst
  ... | lt a<0 | lt -a<0 | _ = Empty.rec (<0-explode {a = a} a<0 -a<0)
  ... | ge a≥0 | ge -a≥0 | _ =
    (λ i → -a≡0 i ·𝕂 b) ∙ ·𝕂-lZero b ∙ (sym -0≡0) ∙ (λ i → -𝕂 (·𝕂-lZero b (~ i))) ∙ (λ i → -𝕂 (a≡0 (~ i) ·𝕂 b))
    where a≡0 : a ≡ 𝟘
          a≡0 = ≥0→≡0 a≥0 -a≥0
          -a≡0 : -𝕂 a ≡ 𝟘
          -a≡0 = (λ i → -𝕂 a≡0 i) ∙ -0≡0

  ·𝕂-neg : (a b : 𝕂) → (a ·𝕂 (-𝕂 b)) ≡ -𝕂 (a ·𝕂 b)
  ·𝕂-neg a b = ·𝕂-Comm a (-𝕂 b) ∙ neg-·𝕂 b a ∙ cong (-𝕂_) (·𝕂-Comm b a)

  neg-·𝕂-neg : (a b : 𝕂) → ((-𝕂 a) ·𝕂 (-𝕂 b)) ≡ a ·𝕂 b
  neg-·𝕂-neg a b = neg-·𝕂 a (-𝕂 b) ∙ cong (-𝕂_) (·𝕂-neg a b) ∙ -𝕂-Involutive (a ·𝕂 b)


{-
  ·𝕂-Assoc : (a b c : 𝕂) → a ·𝕂 (b ·𝕂 c) ≡ (a ·𝕂 b) ·𝕂 c
  ·𝕂-Assoc a b c i with dichotomy𝕂 a 𝟘 | dichotomy𝕂 b 𝟘 | dichotomy𝕂 c 𝟘
  ... | ge _ | ge _ | ge _ = ·𝕂₊-Assoc (abs𝕂 a) (abs𝕂 b) (abs𝕂 c) i .fst
  ... | ge _ | ge _ | lt _ = (·𝕂-neg (abs-𝕂 a) ((abs-𝕂 b) ·𝕂 (abs-𝕂 c)) ∙ (λ i → -𝕂 (·𝕂₊-Assoc (abs𝕂 a) (abs𝕂 b) (abs𝕂 c) i .fst))) i
  ... | lt _ | lt _ | ge _ = {!!}
  ... | lt _ | lt _ | lt _ = {!!}
  ... | ge _ | lt _ | ge _ = {!!}
  ... | ge _ | lt _ | lt _ = {!!}
  ... | lt _ | ge _ | ge _ = {!!}
  ... | lt _ | ge _ | lt _ = {!!}-}
