{-

Order Structure on Dedekind Cuts

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.DedekindCut.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.DedekindCut.Base
open import Classical.Algebra.OrderedField.DedekindCut.Algebra
open import Classical.Algebra.OrderedField.DedekindCut.Signature

private
  variable
    ℓ ℓ' : Level


module Order (decide : LEM)
  (𝒦 : OrderedField ℓ ℓ')(archimedes : isArchimedean (𝒦 . fst))
  where

  private
    K = 𝒦 .fst .fst .fst

  open Powerset decide

  open OrderedFieldStr 𝒦
  open Basics   decide 𝒦
  open Algebra  decide 𝒦 archimedes
  open DedekindCut

  {-

    Strict Ordering

  -}

  _<𝕂_ : 𝕂 → 𝕂 → Type (ℓ-max ℓ ℓ')
  a <𝕂 b = a ≤𝕂 b × ∥ Σ[ q ∈ K ] ((r : K) → r ∈ b .upper → q < r) × q ∈ a .upper ∥

  _>𝕂_ : 𝕂 → 𝕂 → Type (ℓ-max ℓ ℓ')
  a >𝕂 b = b <𝕂 a

  1>𝕂0 : 𝟙 >𝕂 𝟘
  1>𝕂0 = {!!}

  -- Strictness

  <𝕂→≤𝕂 : {a b : 𝕂} → a <𝕂 b → a ≤𝕂 b
  <𝕂→≤𝕂 = {!!}

  <𝕂-arefl : {a b : 𝕂} → a <𝕂 b → a ≡ b → ⊥
  <𝕂-arefl = {!!}

  >𝕂-arefl : {a b : 𝕂} → b <𝕂 a → a ≡ b → ⊥
  >𝕂-arefl = {!!}

  --≤𝕂+≢→<𝕂 : {a b : 𝕂} → a ≤𝕂 b → ¬ a ≡ b → a <𝕂 b
  --≤𝕂+≢→<𝕂 = {!!}

  <𝕂-asym : (a b : 𝕂) → a <𝕂 b → a >𝕂 b → ⊥
  <𝕂-asym = {!!}

  <≤𝕂-asym : (a b : 𝕂) → a <𝕂 b → a ≥𝕂 b → ⊥
  <≤𝕂-asym = {!!}


  data Trichotomy𝕂 (a b : 𝕂) : Type (ℓ-max ℓ ℓ') where
    gt : a >𝕂 b → Trichotomy𝕂 a b
    eq : a ≡ b  → Trichotomy𝕂 a b
    lt : a <𝕂 b → Trichotomy𝕂 a b

  trichotomy𝕂 : (a b : 𝕂) → Trichotomy𝕂 a b
  trichotomy𝕂 = {!!}

  data Dichotomy𝕂 (a b : 𝕂) : Type (ℓ-max ℓ ℓ') where
    ge : a ≥𝕂 b → Dichotomy𝕂 a b
    lt : a <𝕂 b → Dichotomy𝕂 a b

  dichotomy𝕂 : (a b : 𝕂) → Dichotomy𝕂 a b
  dichotomy𝕂 a b = {!!}


  <𝕂-reverse : (a b : 𝕂) → a <𝕂 b → (-𝕂 b) ≤𝕂 (-𝕂 a)
  <𝕂-reverse = {!!}

  -reverse>0 : (a : 𝕂) → a >𝕂 𝟘 → (-𝕂 a) <𝕂 𝟘
  -reverse>0  = {!!}

  -reverse<0 : (a : 𝕂) → a <𝕂 𝟘 → (-𝕂 a) >𝕂 𝟘
  -reverse<0  = {!!}

  <0-reverse : (a : 𝕂) → a <𝕂 𝟘 → (-𝕂 a) ≥𝕂 𝟘
  <0-reverse = {!!}


  +-Pres<0 : (a b : 𝕂) → a <𝕂 𝟘 → b <𝕂 𝟘 → (a +𝕂 b) <𝕂 𝟘
  +-Pres<0 a b = {!!}

  +𝕂-Pres≥0 : (a b : 𝕂) → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → (a +𝕂 b) ≥𝕂 𝟘
  +𝕂-Pres≥0 a b = {!!}


  ·𝕂-Pres>0 : (a b : 𝕂₊) → a .fst >𝕂 𝟘 → b .fst >𝕂 𝟘 → (a ·𝕂₊ b) .fst >𝕂 𝟘
  ·𝕂-Pres>0 a b = {!!}


  -- Two lemmas for convenient case-splitting

  a≥0+-a≥0→a≡0 : {a : 𝕂} → a ≥𝕂 𝟘 → (-𝕂 a) ≥𝕂 𝟘 → a ≡ 𝟘
  a≥0+-a≥0→a≡0 = {!!}

  a<0+-a<0→⊥ : {a : 𝕂} → a <𝕂 𝟘 → (-𝕂 a) <𝕂 𝟘 → ⊥
  a<0+-a<0→⊥ = {!!}

  a>0+-a>0→⊥ : {a : 𝕂} → a >𝕂 𝟘 → (-𝕂 a) >𝕂 𝟘 → ⊥
  a>0+-a>0→⊥ = {!!}


  {-

    Absolute Value

  -}

  -0≡0 : -𝕂 𝟘 ≡ 𝟘
  -0≡0 = sym (+𝕂-rUnit (-𝕂 𝟘)) ∙ +𝕂-lInverse 𝟘

  abs𝕂 : 𝕂 → 𝕂₊
  abs𝕂 a with trichotomy𝕂 a 𝟘
  ... | gt a>0 = a , <𝕂→≤𝕂 {a = 𝟘} {b = a} a>0
  ... | eq a≡0 = 𝟘₊
  ... | lt a<0 = -𝕂 a , subst (_≤𝕂 (-𝕂 a)) -0≡0 (<𝕂-reverse a 𝟘 a<0)

  abs-𝕂 : (a : 𝕂) → abs𝕂 (-𝕂 a) ≡ abs𝕂 a
  abs-𝕂 a with trichotomy𝕂 a 𝟘 | trichotomy𝕂 (-𝕂 a) 𝟘
  ... | gt a>0 | gt -a>0 = Empty.rec (a>0+-a>0→⊥ {a = a} a>0 -a>0)
  ... | lt a<0 | lt -a<0 = Empty.rec (a<0+-a<0→⊥ {a = a} a<0 -a<0)
  ... | eq a≡0 | gt -a>0 = path-𝕂₊ _ _ -a≡0
    where -a≡0 : -𝕂 a ≡ 𝟘
          -a≡0 = (λ i → -𝕂 (a≡0 i)) ∙ -0≡0
  ... | eq a≡0 | eq -a≡0 = refl
  ... | eq a≡0 | lt -a<0 = path-𝕂₊ _ _ -a≡0
    where -a≡0 : -𝕂 (-𝕂 a) ≡ 𝟘
          -a≡0 = (λ i → -𝕂 (-𝕂 (a≡0 i))) ∙ -𝕂-Involutive 𝟘
  ... | gt a>0 | eq -a≡0 = path-𝕂₊ _ _ (sym a≡0)
    where a≡0 : a ≡ 𝟘
          a≡0 = sym (-𝕂-Involutive a) ∙ (λ i → -𝕂 (-a≡0 i)) ∙ -0≡0
  ... | lt a<0 | eq -a≡0 = path-𝕂₊ _ _ (sym -a≡0)
  ... | gt a>0 | lt -a<0 = path-𝕂₊ _ _ (-𝕂-Involutive a)
  ... | lt a<0 | gt -a>0 = path-𝕂₊ _ _ refl


  {-

    Sign

  -}

  sign : 𝕂 → Sign
  sign a with trichotomy𝕂 a 𝟘
  ... | gt a>0 = pos
  ... | eq a≡0 = nul
  ... | lt a<0 = neg

  signed : Sign → 𝕂₊ → 𝕂
  signed pos a = a .fst
  signed nul a = 𝟘
  signed neg a = -𝕂 a .fst


  sign>0 : (a : 𝕂) → a >𝕂 𝟘 → sign a ≡ pos
  sign>0 a a>0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = refl
  ... | eq a≡0 = Empty.rec (<𝕂-arefl a>0 (sym a≡0))
  ... | lt a<0 = Empty.rec (<𝕂-asym 𝟘 a a>0 a<0)

  sign≡0 : (a : 𝕂) → a ≡ 𝟘 → sign a ≡ nul
  sign≡0 a a≡0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = Empty.rec (<𝕂-arefl a>0 (sym a≡0))
  ... | eq a≡0 = refl
  ... | lt a<0 = Empty.rec (<𝕂-arefl a<0 a≡0)

  sign<0 : (a : 𝕂) → a <𝕂 𝟘 → sign a ≡ neg
  sign<0 a a<0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = Empty.rec (<𝕂-asym 𝟘 a a>0 a<0)
  ... | eq a≡0 = Empty.rec (<𝕂-arefl a<0 a≡0)
  ... | lt a<0 = refl

  sign≥0 : (a : 𝕂) → a ≥𝕂 𝟘 → sign a ≥0s
  sign≥0 a a≥0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = _
  ... | eq a≡0 = _
  ... | lt a<0 = Empty.rec (<≤𝕂-asym a 𝟘 a<0 a≥0)

  sign𝟘 : sign 𝟘 ≡ nul
  sign𝟘 = sign≡0 _ refl

  sign𝟙 : sign 𝟙 ≡ pos
  sign𝟙 = sign>0 𝟙 1>𝕂0


  -sign : (a : 𝕂) → sign (-𝕂 a) ≡ -s (sign a)
  -sign a with trichotomy𝕂 a 𝟘
  ... | gt a>0 = sign<0 (-𝕂 a) (-reverse>0 a a>0)
  ... | eq a≡0 = sign≡0 (-𝕂 a) ((λ i → -𝕂 (a≡0 i)) ∙ -0≡0)
  ... | lt a<0 = sign>0 (-𝕂 a) (-reverse<0 a a<0)


  signed𝟘 : (s : Sign) → signed s 𝟘₊ ≡ 𝟘
  signed𝟘 pos = refl
  signed𝟘 nul = refl
  signed𝟘 neg = -0≡0

  signed- : (s : Sign)(a : 𝕂₊) → signed (-s s) a ≡ -𝕂 (signed s a)
  signed- pos a = refl
  signed- nul a = sym -0≡0
  signed- neg a = sym (-𝕂-Involutive _)


  abs>0 : (a : 𝕂) → a >𝕂 𝟘 → abs𝕂 a .fst >𝕂 𝟘
  abs>0 a a>0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = a>0
  ... | eq a≡0 = Empty.rec (<𝕂-arefl a>0 (sym a≡0))
  ... | lt a<0 = Empty.rec (<𝕂-asym a 𝟘 a<0 a>0)

  abs<0 : (a : 𝕂) → a <𝕂 𝟘 → abs𝕂 a .fst >𝕂 𝟘
  abs<0 a a<0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = Empty.rec (<𝕂-asym a 𝟘 a<0 a>0)
  ... | eq a≡0 = Empty.rec (<𝕂-arefl a<0 a≡0)
  ... | lt a<0 = -reverse<0 a a<0

  abs≥0 : (a : 𝕂) → a ≥𝕂 𝟘 → abs𝕂 a .fst ≡ a
  abs≥0 a a≥0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = refl
  ... | eq a≡0 = sym a≡0
  ... | lt a<0 = Empty.rec (<≤𝕂-asym a 𝟘 a<0 a≥0)


  abs𝟘 : abs𝕂 𝟘 ≡ 𝟘₊
  abs𝟘 = path-𝕂₊ _ _ (abs≥0 𝟘 (𝟘₊ .snd))

  abs≡0 : (a : 𝕂) → a ≡ 𝟘 → abs𝕂 a ≡ 𝟘₊
  abs≡0 a a≡0 = cong abs𝕂 a≡0 ∙ abs𝟘

  abs𝟙 : abs𝕂 𝟙 ≡ 𝟙₊
  abs𝟙 = path-𝕂₊ _ _ (abs≥0 𝟙 (𝟙₊ .snd))


  sign-abs-≡ : (a : 𝕂) → signed (sign a) (abs𝕂 a) ≡ a
  sign-abs-≡ a with trichotomy𝕂 a 𝟘
  ... | gt a>0 = refl
  ... | eq a≡0 = sym a≡0
  ... | lt a<0 = -𝕂-Involutive a


  abs-signed : (s : Sign)(a : 𝕂₊) → ¬ s ≡ nul → abs𝕂 (signed s a) ≡ a
  abs-signed pos (a , a≥0) ¬s≡nul with trichotomy𝕂 a 𝟘
  ... | gt a>0 = path-𝕂₊ _ _ refl
  ... | eq a≡0 = path-𝕂₊ _ _ (sym a≡0)
  ... | lt a<0 = Empty.rec (<≤𝕂-asym a 𝟘 a<0 a≥0)
  abs-signed nul _ ¬s≡nul = Empty.rec (¬s≡nul refl)
  abs-signed neg (a , a≥0) ¬s≡nul with trichotomy𝕂 a 𝟘
  ... | gt a>0 = path-𝕂₊ _ _ ((λ i → abs-𝕂 a i .fst) ∙ abs≥0 a a≥0)
  ... | eq a≡0 = path-𝕂₊ _ _ ((λ i → abs-𝕂 a i .fst) ∙ abs≥0 a a≥0)
  ... | lt a<0 = Empty.rec (<≤𝕂-asym a 𝟘 a<0 a≥0)

  sign-signed : (s : Sign)(a : 𝕂₊) → ¬ a .fst ≡ 𝟘 → sign (signed s a) ≡ s
  sign-signed pos (a , a≥0) ¬a≡0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = refl
  ... | eq a≡0 = Empty.rec (¬a≡0 a≡0)
  ... | lt a<0 = Empty.rec (<≤𝕂-asym a 𝟘 a<0 a≥0)
  sign-signed nul (a , a≥0) ¬a≡0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = sign≡0 𝟘 refl
  ... | eq a≡0 = Empty.rec (¬a≡0 a≡0)
  ... | lt a<0 = Empty.rec (<≤𝕂-asym a 𝟘 a<0 a≥0)
  sign-signed neg (a , a≥0) ¬a≡0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = sign<0 (-𝕂 a) (-reverse>0 a a>0)
  ... | eq a≡0 = Empty.rec (¬a≡0 a≡0)
  ... | lt a<0 = Empty.rec (<≤𝕂-asym a 𝟘 a<0 a≥0)


  {-

    Full Multiplication

  -}

  _·𝕂_ : 𝕂 → 𝕂 → 𝕂
  (a ·𝕂 b) = signed (sign a ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b)


  private
    lZeroSign : (a : 𝕂) → sign 𝟘 ≡ sign 𝟘 ·s sign a
    lZeroSign a = sign𝟘 ∙ (λ i → sign𝟘 (~ i) ·s sign a)

    rZeroSign : (a : 𝕂) → sign 𝟘 ≡ sign a ·s sign 𝟘
    rZeroSign a = lZeroSign a ∙ ·s-Comm (sign 𝟘) (sign a)

    lZero : (a : 𝕂) → abs𝕂 𝟘 ≡ abs𝕂 𝟘 ·𝕂₊ abs𝕂 a
    lZero a = abs𝟘 ∙ sym (·𝕂₊-lZero (abs𝕂 a)) ∙ (λ i → abs𝟘 (~ i) ·𝕂₊ abs𝕂 a)

    rZero : (a : 𝕂) → abs𝕂 𝟘 ≡ abs𝕂 a ·𝕂₊ abs𝕂 𝟘
    rZero a = lZero a ∙ ·𝕂₊-Comm (abs𝕂 𝟘) (abs𝕂 a)

  sign· : (a b : 𝕂) → sign (a ·𝕂 b) ≡ sign a ·s sign b
  sign· a b = case-split (trichotomy𝕂 a 𝟘) (trichotomy𝕂 b 𝟘)
    where
    case-split : Trichotomy𝕂 a 𝟘 → Trichotomy𝕂 b 𝟘 → sign (a ·𝕂 b) ≡ sign a ·s sign b
    case-split (gt a>0) (gt b>0) =
      sign-signed _ (abs𝕂 a ·𝕂₊ abs𝕂 b) (>𝕂-arefl (·𝕂-Pres>0 (abs𝕂 a) (abs𝕂 b) (abs>0 a a>0) (abs>0 b b>0)))
    case-split (lt a<0) (lt b<0) =
      sign-signed _ (abs𝕂 a ·𝕂₊ abs𝕂 b) (>𝕂-arefl (·𝕂-Pres>0 (abs𝕂 a) (abs𝕂 b) (abs<0 a a<0) (abs<0 b b<0)))
    case-split (gt a>0) (lt b<0) =
      sign-signed _ (abs𝕂 a ·𝕂₊ abs𝕂 b) (>𝕂-arefl (·𝕂-Pres>0 (abs𝕂 a) (abs𝕂 b) (abs>0 a a>0) (abs<0 b b<0)))
    case-split (lt a<0) (gt b>0) =
      sign-signed _ (abs𝕂 a ·𝕂₊ abs𝕂 b) (>𝕂-arefl (·𝕂-Pres>0 (abs𝕂 a) (abs𝕂 b) (abs<0 a a<0) (abs>0 b b>0)))
    case-split (eq a≡0) _ =
      (λ i → sign (signed (sign≡0 a a≡0 i ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ lZeroSign b ∙ (λ i → sign (a≡0 (~ i)) ·s sign b)
    case-split _ (eq b≡0) =
      (λ i → sign (signed (sign a ·s sign≡0 b b≡0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ (λ i → sign (signed (·s-Comm (sign a) nul i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ rZeroSign a ∙ (λ i → sign a ·s sign (b≡0 (~ i)))

  abs· : (a b : 𝕂) → abs𝕂 (a ·𝕂 b) ≡ (abs𝕂 a ·𝕂₊ abs𝕂 b)
  abs· a b = case-split (trichotomy𝕂 a 𝟘) (trichotomy𝕂 b 𝟘)
    where
    case-split : Trichotomy𝕂 a 𝟘 → Trichotomy𝕂 b 𝟘 → abs𝕂 (a ·𝕂 b) ≡ (abs𝕂 a ·𝕂₊ abs𝕂 b)
    case-split (gt a>0) (gt b>0) =
      (λ i → abs𝕂 (signed (sign>0 a a>0 i ·s sign>0 b b>0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ abs-signed _ _ pos≢nul
    case-split (lt a<0) (lt b<0) =
      (λ i → abs𝕂 (signed (sign<0 a a<0 i ·s sign<0 b b<0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ abs-signed _ _ pos≢nul
    case-split (gt a>0) (lt b<0) =
      (λ i → abs𝕂 (signed (sign>0 a a>0 i ·s sign<0 b b<0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ abs-signed _ _ neg≢nul
    case-split (lt a<0) (gt b>0) =
      (λ i → abs𝕂 (signed (sign<0 a a<0 i ·s sign>0 b b>0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ abs-signed _ _ neg≢nul
    case-split (eq a≡0) _ =
      (λ i → abs𝕂 (signed (sign≡0 a a≡0 i ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ lZero b ∙ (λ i → abs𝕂 (a≡0 (~ i)) ·𝕂₊ abs𝕂 b)
    case-split _ (eq b≡0) =
      (λ i → abs𝕂 (signed (sign a ·s sign≡0 b b≡0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ (λ i → abs𝕂 (signed (·s-Comm (sign a) nul i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ rZero a ∙ (λ i → abs𝕂 a ·𝕂₊ abs𝕂 (b≡0 (~ i)))


  ·𝕂-Comm : (a b : 𝕂) → a ·𝕂 b ≡ b ·𝕂 a
  ·𝕂-Comm a b i = signed (·s-Comm (sign a) (sign b) i) (·𝕂₊-Comm (abs𝕂 a) (abs𝕂 b) i)

  ·𝕂-Assoc : (a b c : 𝕂) → a ·𝕂 (b ·𝕂 c) ≡ (a ·𝕂 b) ·𝕂 c
  ·𝕂-Assoc a b c =
    let p = λ i → signed (sign a ·s sign· b c i) (abs𝕂 a ·𝕂₊ abs· b c i)
        q = λ i → signed (sign· a b i ·s sign c) (abs· a b i ·𝕂₊ abs𝕂 c)
        r = λ i → signed (·s-Assoc (sign a) (sign b) (sign c) i) (·𝕂₊-Assoc (abs𝕂 a) (abs𝕂 b) (abs𝕂 c) i)
    in  p ∙ r ∙ sym q


  ·𝕂-rUnit : (a : 𝕂) → a ·𝕂 𝟙 ≡ a
  ·𝕂-rUnit a = (λ i → signed (sign-path i) (abs𝕂 a ·𝕂₊ abs𝟙 i))
    ∙ (λ i → signed (sign a) (·𝕂₊-rUnit (abs𝕂 a) i))
    ∙ sign-abs-≡ a
    where
    sign-path : sign a ·s sign 𝟙 ≡ sign a
    sign-path = (λ i → sign a ·s sign𝟙 i) ∙ ·s-rUnit (sign a)

  ·𝕂-rZero : (a : 𝕂) → a ·𝕂 𝟘 ≡ 𝟘
  ·𝕂-rZero a = (λ i → signed (sign a ·s sign 𝟘) (abs𝕂 a ·𝕂₊ abs𝟘 i))
    ∙ (λ i → signed (sign a ·s sign 𝟘) (·𝕂₊-rZero (abs𝕂 a) i))
    ∙ signed𝟘 (sign a ·s sign 𝟘)

  ·𝕂-lZero : (a : 𝕂) → 𝟘 ·𝕂 a ≡ 𝟘
  ·𝕂-lZero a = ·𝕂-Comm 𝟘 a ∙ ·𝕂-rZero a


  neg-·𝕂 : (a b : 𝕂) → ((-𝕂 a) ·𝕂 b) ≡ -𝕂 (a ·𝕂 b)
  neg-·𝕂  a b = (λ i → signed (-sign a i ·s sign b) (abs-𝕂 a i ·𝕂₊ abs𝕂 b))
    ∙ (λ i → signed (-s-· (sign a) (sign b) i) (abs𝕂 a ·𝕂₊ abs𝕂 b))
    ∙ signed- (sign a ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b)

  ·𝕂-neg : (a b : 𝕂) → (a ·𝕂 (-𝕂 b)) ≡ -𝕂 (a ·𝕂 b)
  ·𝕂-neg a b = ·𝕂-Comm a (-𝕂 b) ∙ neg-·𝕂 b a ∙ cong (-𝕂_) (·𝕂-Comm b a)

  neg-·𝕂-neg : (a b : 𝕂) → ((-𝕂 a) ·𝕂 (-𝕂 b)) ≡ a ·𝕂 b
  neg-·𝕂-neg a b = neg-·𝕂 a (-𝕂 b) ∙ cong (-𝕂_) (·𝕂-neg a b) ∙ -𝕂-Involutive (a ·𝕂 b)


  private
    ·pos-helper : (a b : 𝕂) → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → a ·𝕂 b ≡ ((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) .fst
    ·pos-helper a b a≥0 b≥0 = case-split (trichotomy𝕂 a 𝟘) (trichotomy𝕂 b 𝟘)
      where
      case-split : Trichotomy𝕂 a 𝟘 → Trichotomy𝕂 b 𝟘 → a ·𝕂 b ≡ ((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) .fst
      case-split (lt a<0) _ = Empty.rec (<≤𝕂-asym a 𝟘 a<0 a≥0)
      case-split _ (lt b<0) = Empty.rec (<≤𝕂-asym b 𝟘 b<0 b≥0)
      case-split (eq a≡0) _ =
          (λ i → a≡0 i ·𝕂 b)
        ∙ ·𝕂-lZero b
        ∙ (λ i → (·𝕂₊-lZero (abs𝕂 b) (~ i)) .fst)
        ∙ (λ i → (abs𝟘 (~ i) ·𝕂₊ (abs𝕂 b)) .fst)
        ∙ (λ i → (abs𝕂 (a≡0 (~ i)) ·𝕂₊ (abs𝕂 b)) .fst)
      case-split _ (eq b≡0) =
        (λ i → a ·𝕂 b≡0 i)
        ∙ ·𝕂-rZero a
        ∙ (λ i → (·𝕂₊-rZero (abs𝕂 a) (~ i)) .fst)
        ∙ (λ i → ((abs𝕂 a) ·𝕂₊ abs𝟘 (~ i)) .fst)
        ∙ (λ i → ((abs𝕂 a) ·𝕂₊ abs𝕂 (b≡0 (~ i))) .fst)
      case-split (gt a>0) (gt b>0) i =
        signed ((sign>0 a a>0 i) ·s(sign>0 b b>0 i)) ((abs𝕂 a) ·𝕂₊ (abs𝕂 b))

    +pos-helper : (a b : 𝕂) → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → abs𝕂 (a +𝕂 b) ≡ ((abs𝕂 a) +𝕂₊ (abs𝕂 b))
    +pos-helper a b a≥0 b≥0 = path-𝕂₊ (abs𝕂 (a +𝕂 b)) _ path
      where a+b≥0 : (a +𝕂 b) ≥𝕂 𝟘
            a+b≥0 = +𝕂-Pres≥0 a b a≥0 b≥0
            path : abs𝕂 (a +𝕂 b) .fst ≡ ((abs𝕂 a) +𝕂₊ (abs𝕂 b)) .fst
            path = abs≥0 (a +𝕂 b) a+b≥0 ∙ (λ i → abs≥0 a a≥0 (~ i) +𝕂 abs≥0 b b≥0 (~ i))

  ·𝕂-lDistb-PosPosPos : (a b c : 𝕂)
    → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → c ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂-lDistb-PosPosPos a b c a≥0 b≥0 c≥0 =
      (λ i → ·pos-helper a b a≥0 b≥0 i +𝕂 ·pos-helper a c a≥0 c≥0 i)
    ∙ (λ i → ·𝕂₊-lDistrib (abs𝕂 a) (abs𝕂 b) (abs𝕂 c) i .fst)
    ∙ (λ i → ((abs𝕂 a) ·𝕂₊ +pos-helper b c b≥0 c≥0 (~ i)) .fst)
    ∙ sym (·pos-helper a (b +𝕂 c) a≥0 b+c≥0)
    where
    b+c≥0 : (b +𝕂 c) ≥𝕂 𝟘
    b+c≥0 = +𝕂-Pres≥0 b c b≥0 c≥0

  ·𝕂-lDistb-PosPosNeg : (a b c : 𝕂)
    → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → c <𝕂 𝟘 → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂-lDistb-PosPosNeg a b c a≥0 b≥0 c<0 b+c≥0 = (λ i → path1 (~ i) +𝕂 (a ·𝕂 c)) ∙ path2
    where
    path1 : (a ·𝕂 (b +𝕂 c)) +𝕂 (-𝕂 (a ·𝕂 c)) ≡ a ·𝕂 b
    path1 = (λ i → (a ·𝕂 (b +𝕂 c)) +𝕂 ·𝕂-neg a c (~ i))
      ∙ ·𝕂-lDistb-PosPosPos a (b +𝕂 c) (-𝕂 c) a≥0 b+c≥0 (<0-reverse c c<0)
      ∙ (λ i → a ·𝕂 +𝕂-Assoc b c (-𝕂 c) (~ i))
      ∙ (λ i → a ·𝕂 (b +𝕂 +𝕂-rInverse c i)) ∙ (λ i → a ·𝕂 (+𝕂-rUnit b i))
    path2 : ((a ·𝕂 (b +𝕂 c)) +𝕂 (-𝕂 (a ·𝕂 c))) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
    path2 = sym (+𝕂-Assoc _ _ _) ∙ (λ i → (a ·𝕂 (b +𝕂 c)) +𝕂 +𝕂-lInverse (a ·𝕂 c) i) ∙ +𝕂-rUnit _

  ·𝕂-lDistb-PosPos : (a b c : 𝕂)
    → a ≥𝕂 𝟘 → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂-lDistb-PosPos a b c a≥0 b+c≥0 = case-split (dichotomy𝕂 b 𝟘) (dichotomy𝕂 c 𝟘)
    where
    case-split : Dichotomy𝕂 b 𝟘 → Dichotomy𝕂 c 𝟘 → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
    case-split (ge b≥0) (ge c≥0) = ·𝕂-lDistb-PosPosPos a b c a≥0 b≥0 c≥0
    case-split (lt b<0) (ge c≥0) = +𝕂-Comm _ _
      ∙ (λ i → ·𝕂-lDistb-PosPosNeg a c b a≥0 c≥0 b<0 c+b≥0 i)
      ∙ (λ i → a ·𝕂 +𝕂-Comm c b i)
      where c+b≥0 : (c +𝕂 b) ≥𝕂 𝟘
            c+b≥0 = subst (_≥𝕂 𝟘) (+𝕂-Comm b c) b+c≥0
    case-split (ge b≥0) (lt c<0) = ·𝕂-lDistb-PosPosNeg a b c a≥0 b≥0 c<0 b+c≥0
    case-split (lt b<0) (lt c<0) = Empty.rec (<≤𝕂-asym (b +𝕂 c) 𝟘 (+-Pres<0 b c b<0 c<0) b+c≥0)

  private
    alg-helper' : (a b c d : 𝕂) → (a +𝕂 b) +𝕂 (c +𝕂 d) ≡ (a +𝕂 c) +𝕂 (b +𝕂 d)
    alg-helper' a b c d = +𝕂-Assoc (a +𝕂 b) c d
      ∙ (λ i → +𝕂-Assoc a b c (~ i) +𝕂 d)
      ∙ (λ i → (a +𝕂 +𝕂-Comm b c i) +𝕂 d)
      ∙ (λ i → +𝕂-Assoc a c b i +𝕂 d)
      ∙ sym (+𝕂-Assoc (a +𝕂 c) b d)

    alg-helper : (a b : 𝕂) → -𝕂 (a +𝕂 b) ≡ (-𝕂 a) +𝕂 (-𝕂 b)
    alg-helper a b = sym (+𝕂-rUnit (-𝕂 (a +𝕂 b)))
      ∙ (λ i → (-𝕂 (a +𝕂 b)) +𝕂 path (~ i))
      ∙ +𝕂-Assoc _ _ _
      ∙ (λ i → +𝕂-lInverse (a +𝕂 b) i +𝕂 ((-𝕂 a) +𝕂 (-𝕂 b)))
      ∙ +𝕂-lUnit ((-𝕂 a) +𝕂 (-𝕂 b))
      where
      path : (a +𝕂 b) +𝕂 ((-𝕂 a) +𝕂 (-𝕂 b)) ≡ 𝟘
      path = alg-helper' _ _ _ _ ∙ (λ i → +𝕂-rInverse a i +𝕂 +𝕂-rInverse b i) ∙ +𝕂-rUnit 𝟘

  ·𝕂-lDistb-NegPos : (a b c : 𝕂)
    → a <𝕂 𝟘 → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂-lDistb-NegPos a b c a<0 b+c≥0 =
    sym (-𝕂-Involutive _) ∙ (λ i → -𝕂 path i) ∙ -𝕂-Involutive _
    where
    path : -𝕂 ((a ·𝕂 b) +𝕂 (a ·𝕂 c)) ≡ -𝕂 (a ·𝕂 (b +𝕂 c))
    path = alg-helper (a ·𝕂 b) (a ·𝕂 c)
      ∙ (λ i → neg-·𝕂 a b (~ i) +𝕂 neg-·𝕂 a c (~ i))
      ∙ ·𝕂-lDistb-PosPos (-𝕂 a) b c (<0-reverse a a<0) b+c≥0
      ∙ neg-·𝕂 a (b +𝕂 c)

  ·𝕂-lDistb-Pos : (a b c : 𝕂)
    → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂-lDistb-Pos a b c b+c≥0 = case-split (dichotomy𝕂 a 𝟘)
    where
    case-split : Dichotomy𝕂 a 𝟘 → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
    case-split (ge a≥0) = ·𝕂-lDistb-PosPos a b c a≥0 b+c≥0
    case-split (lt a<0) = ·𝕂-lDistb-NegPos a b c a<0 b+c≥0

  ·𝕂-lDistb-Neg : (a b c : 𝕂)
    → (b +𝕂 c) <𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂-lDistb-Neg a b c b+c<0 =
    sym (-𝕂-Involutive _) ∙ (λ i → -𝕂 path i) ∙ -𝕂-Involutive _
    where
    -b+-k≥0 : ((-𝕂 b) +𝕂 (-𝕂 c)) ≥𝕂 𝟘
    -b+-k≥0 = subst (_≥𝕂 𝟘) (alg-helper b c) (<0-reverse (b +𝕂 c) b+c<0)
    path : -𝕂 ((a ·𝕂 b) +𝕂 (a ·𝕂 c)) ≡ -𝕂 (a ·𝕂 (b +𝕂 c))
    path = alg-helper (a ·𝕂 b) (a ·𝕂 c)
      ∙ (λ i → ·𝕂-neg a b (~ i) +𝕂 ·𝕂-neg a c (~ i))
      ∙ ·𝕂-lDistb-Pos a (-𝕂 b) (-𝕂 c) -b+-k≥0
      ∙ (λ i → a ·𝕂 alg-helper b c (~ i))
      ∙ ·𝕂-neg a (b +𝕂 c)

  ·𝕂-lDistb : (a b c : 𝕂) → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂-lDistb a b c = case-split (dichotomy𝕂 (b +𝕂 c) 𝟘)
    where
    case-split : Dichotomy𝕂 (b +𝕂 c) 𝟘 → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
    case-split (ge b+c≥0) = ·𝕂-lDistb-Pos a b c b+c≥0
    case-split (lt b+c<0) = ·𝕂-lDistb-Neg a b c b+c<0


  {-

    Commutative Ring Instance

  -}

  𝕂CommRing : CommRing (ℓ-max ℓ ℓ')
  𝕂CommRing = makeCommRing {R = 𝕂}
      𝟘 𝟙 _+𝕂_ _·𝕂_ -𝕂_ isSet𝕂
    +𝕂-Assoc +𝕂-rUnit +𝕂-rInverse +𝕂-Comm
    ·𝕂-Assoc ·𝕂-rUnit (λ x y z → sym (·𝕂-lDistb x y z)) ·𝕂-Comm
