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

  Sign : Type
  Sign = Bool

  pattern pos = false
  pattern neg = true

  sign : 𝕂 → Sign
  sign a with dichotomy𝕂 a 𝟘
  ... | ge a≥0 = pos
  ... | lt a<0 = neg

  signed : Sign → 𝕂₊ → 𝕂
  signed pos a = a .fst
  signed neg a = -𝕂 a .fst


  sign-abs-≡ : (a : 𝕂) → signed (sign a) (abs𝕂 a) ≡ a
  sign-abs-≡ = {!!}

  abs-signed : (s : Sign)(a : 𝕂₊) → abs𝕂 (signed s a) ≡ a
  abs-signed = {!!}

  sign-signed : (s : Sign)(a : 𝕂₊) → sign (signed s a) ≡ s
  sign-signed = {!!}

  sign≥0 : (a : 𝕂) → a ≥𝕂 𝟘 → sign a ≡ pos
  sign≥0 = {!!}

  sign<0 : (a : 𝕂) → a <𝕂 𝟘 → sign a ≡ neg
  sign<0 = {!!}


  --signed0 : (s : Sign) → signed s 𝟘₊ ≡ s
  --signed0 = {!!}


  {-

    Multiplication

  -}

  _·s_ : Sign → Sign → Sign
  _·s_ = _⊕_

  _·𝕂_ : 𝕂 → 𝕂 → 𝕂
  (a ·𝕂 b) = signed (sign a ·s sign b) ((abs𝕂 a) ·𝕂₊ (abs𝕂 b))


  ·𝕂-Comm : (a b : 𝕂) → a ·𝕂 b ≡ b ·𝕂 a
  ·𝕂-Comm a b i = signed (⊕-comm (sign a) (sign b) i) (·𝕂₊-Comm (abs𝕂 a) (abs𝕂 b) i)

  ·𝕂-Assoc : (a b c : 𝕂) → a ·𝕂 (b ·𝕂 c) ≡ (a ·𝕂 b) ·𝕂 c
  ·𝕂-Assoc a b c =
    let left≡   = λ i → signed (sign a ·s sign-signed (sign b ·s sign c) ((abs𝕂 b) ·𝕂₊ (abs𝕂 c)) i)
          ((abs𝕂 a) ·𝕂₊ abs-signed (sign b ·s sign c) ((abs𝕂 b) ·𝕂₊ (abs𝕂 c)) i)
        right≡  = λ i → signed (sign-signed (sign a ·s sign b) ((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) i ·s sign c)
          (abs-signed (sign a ·s sign b) ((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) i ·𝕂₊ (abs𝕂 c))
        middle≡ = λ i → signed (⊕-assoc (sign a) (sign b) (sign c) i) (·𝕂₊-Assoc (abs𝕂 a) (abs𝕂 b) (abs𝕂 c) i)
    in  left≡ ∙ middle≡ ∙ sym right≡


  ·𝕂-lDistb-PosPos : (a b c : 𝕂)
    → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → c ≥𝕂 𝟘 → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂-lDistb-PosPos = {!!}

  ·𝕂-lDistb-PosNeg : (a b c : 𝕂)
    → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → c <𝕂 𝟘 → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂-lDistb-PosNeg a b c = {!!}
    where
    helper1 : (a ·𝕂 (b +𝕂 c)) +𝕂 (a ·𝕂 (-𝕂 c)) ≡ a ·𝕂 ((b +𝕂 c) +𝕂 (-𝕂 c))
    helper1 = {!!}
    helper2 : a ·𝕂 ((b +𝕂 c) +𝕂 (-𝕂 c)) ≡ a ·𝕂 b
    helper2 = {!!}

  ·𝕂-lDistb-Pos : (a b c : 𝕂)
    → a ≥𝕂 𝟘 → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂-lDistb-Pos a b c = {!!}

