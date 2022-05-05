{-

Order Structure on Dedekind Cuts

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.DedekindCut.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Bool
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


  -- Strictness

  <𝕂→≤𝕂 : {a b : 𝕂} → a <𝕂 b → a ≤𝕂 b
  <𝕂→≤𝕂 = {!!}

  <𝕂→arefl : {a b : 𝕂} → a <𝕂 b → a ≡ b → ⊥
  <𝕂→arefl = {!!}

  ≤𝕂+≢→<𝕂 : {a b : 𝕂} → a ≤𝕂 b → ¬ a ≡ b → a <𝕂 b
  ≤𝕂+≢→<𝕂 = {!!}

  data Trichotomy𝕂 (a b : 𝕂) : Type (ℓ-max ℓ ℓ') where
    gt : a >𝕂 b → Trichotomy𝕂 a b
    eq : a ≡ b → Trichotomy𝕂 a b
    lt : a <𝕂 b → Trichotomy𝕂 a b

  trichotomy𝕂 : (a b : 𝕂) → Trichotomy𝕂 a b
  trichotomy𝕂 = {!!}

  -- Properties

  data Dichotomy𝕂 (a b : 𝕂) : Type (ℓ-max ℓ ℓ') where
    ge : a ≥𝕂 b → Dichotomy𝕂 a b
    lt : a <𝕂 b → Dichotomy𝕂 a b

  dichotomy𝕂 : (a b : 𝕂) → Dichotomy𝕂 a b
  dichotomy𝕂 = {!!}


  <𝕂-reverse : (a b : 𝕂) → a <𝕂 b → (-𝕂 b) ≤𝕂 (-𝕂 a)
  <𝕂-reverse = {!!}

  <𝕂-asym : (a b : 𝕂) → a <𝕂 b → a >𝕂 b → ⊥
  <𝕂-asym = {!!}

  <≤𝕂-asym : (a b : 𝕂) → a <𝕂 b → a ≥𝕂 b → ⊥
  <≤𝕂-asym = {!!}

  -reverse<0 : (a : 𝕂) → a <𝕂 𝟘 → (-𝕂 a) >𝕂 𝟘
  -reverse<0  = {!!}

  -reverse>0 : (a : 𝕂) → a >𝕂 𝟘 → (-𝕂 a) <𝕂 𝟘
  -reverse>0  = {!!}

  <0-reverse : (a : 𝕂) → a <𝕂 𝟘 → (-𝕂 a) ≥𝕂 𝟘
  <0-reverse = {!!}

  ≥0-reverse : (a : 𝕂) → a ≥𝕂 𝟘 → (-𝕂 a) <𝕂 𝟘
  ≥0-reverse = {!!}

  +-Pres<0 : (a b : 𝕂) → a <𝕂 𝟘 → b <𝕂 𝟘 → (a +𝕂 b) <𝕂 𝟘
  +-Pres<0 a b = {!!}

  +𝕂-Pres≥0 : (a b : 𝕂) → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → (a +𝕂 b) ≥𝕂 𝟘
  +𝕂-Pres≥0 a b = {!!}

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
  ... | eq a≡0 = Empty.rec (<𝕂→arefl a>0 (sym a≡0))
  ... | lt a<0 = Empty.rec (<𝕂-asym 𝟘 a a>0 a<0)

  sign≡0 : (a : 𝕂) → a ≡ 𝟘 → sign a ≡ nul
  sign≡0 a a≡0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = Empty.rec (<𝕂→arefl a>0 (sym a≡0))
  ... | eq a≡0 = refl
  ... | lt a<0 = Empty.rec (<𝕂→arefl a<0 a≡0)

  sign<0 : (a : 𝕂) → a <𝕂 𝟘 → sign a ≡ neg
  sign<0 a a<0 with trichotomy𝕂 a 𝟘
  ... | gt a>0 = Empty.rec (<𝕂-asym 𝟘 a a>0 a<0)
  ... | eq a≡0 = Empty.rec (<𝕂→arefl a<0 a≡0)
  ... | lt a<0 = refl


  -sign : (a : 𝕂) → sign (-𝕂 a) ≡ -s (sign a)
  -sign a with trichotomy𝕂 a 𝟘
  ... | gt a>0 = sign<0 (-𝕂 a) (-reverse>0 a a>0)
  ... | eq a≡0 = {!!}
  ... | lt a<0 = {!!}


  signed- : (s : Sign)(a : 𝕂₊) → signed (-s s) a ≡ -𝕂 (signed s a)
  signed- pos a = refl
  signed- nul a = sym -0≡0
  signed- neg a = sym (-𝕂-Involutive _)

  sign-abs-≡ : (a : 𝕂) → signed (sign a) (abs𝕂 a) ≡ a
  sign-abs-≡ = {!!}

  abs-signed : (s : Sign)(a : 𝕂₊) → abs𝕂 (signed s a) ≡ a
  abs-signed = {!!}

  sign-signed : (s : Sign)(a : 𝕂₊) → sign (signed s a) ≡ s
  sign-signed = {!!}

  abs𝟘 : abs𝕂 𝟘 ≡ 𝟘₊
  abs𝟘 = {!!}

  signed𝟘 : (s : Sign) → signed s 𝟘₊ ≡ 𝟘
  signed𝟘 = {!!}

  sign𝟙 : sign 𝟙 ≡ pos
  sign𝟙 = {!!}

  abs𝟙 : abs𝕂 𝟙 ≡ 𝟙₊
  abs𝟙 = {!!}


  {-

    Full Multiplication

  -}

  _·𝕂_ : 𝕂 → 𝕂 → 𝕂
  (a ·𝕂 b) = signed (sign a ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b)


  ·𝕂-Comm : (a b : 𝕂) → a ·𝕂 b ≡ b ·𝕂 a
  ·𝕂-Comm a b i = signed (·s-Comm (sign a) (sign b) i) (·𝕂₊-Comm (abs𝕂 a) (abs𝕂 b) i)

  ·𝕂-Assoc : (a b c : 𝕂) → a ·𝕂 (b ·𝕂 c) ≡ (a ·𝕂 b) ·𝕂 c
  ·𝕂-Assoc a b c =
    let left≡   = λ i → signed (sign a ·s sign-signed (sign b ·s sign c) (abs𝕂 b ·𝕂₊ abs𝕂 c) i)
          ((abs𝕂 a) ·𝕂₊ abs-signed (sign b ·s sign c) (abs𝕂 b ·𝕂₊ abs𝕂 c) i)
        right≡  = λ i → signed (sign-signed (sign a ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b) i ·s sign c)
          (abs-signed (sign a ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b) i ·𝕂₊ abs𝕂 c)
        middle≡ = λ i → signed (·s-Assoc (sign a) (sign b) (sign c) i) (·𝕂₊-Assoc (abs𝕂 a) (abs𝕂 b) (abs𝕂 c) i)
    in  left≡ ∙ middle≡ ∙ sym right≡


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
    ·pos-helper = {!!}

    +pos-helper : (a b : 𝕂) → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → abs𝕂 (a +𝕂 b) ≡ ((abs𝕂 a) +𝕂₊ (abs𝕂 b))
    +pos-helper = {!!}

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
    alg-helper : (a b : 𝕂) → -𝕂 (a +𝕂 b) ≡ (-𝕂 a) +𝕂 (-𝕂 b)
    alg-helper = {!!}

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
