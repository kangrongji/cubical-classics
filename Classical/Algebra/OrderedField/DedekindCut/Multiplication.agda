{-

Multiplicative Structure on Dedekind Cuts

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.DedekindCut.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Algebra.CommRing

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Algebra.OrderedRing
open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.DedekindCut.Base
open import Classical.Algebra.OrderedField.DedekindCut.Algebra
open import Classical.Algebra.OrderedField.DedekindCut.Signature
open import Classical.Algebra.OrderedField.DedekindCut.Order

private
  variable
    ℓ ℓ' : Level


module Multiplication (decide : LEM)
  (𝒦 : OrderedField ℓ ℓ')(archimedes : isArchimedean (𝒦 . fst))
  where

  private
    K = 𝒦 .fst .fst .fst

  open Powerset decide

  open OrderedFieldStr 𝒦
  open Basics   decide 𝒦
  open Algebra  decide 𝒦 archimedes
  open Order    decide 𝒦 archimedes
  open DedekindCut


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


  {-

    Ordered Ring Instance

  -}

  ·𝕂'-Pres>0 : (a b : 𝕂) → a >𝕂 𝟘 → b >𝕂 𝟘 → (a ·𝕂 b) >𝕂 𝟘
  ·𝕂'-Pres>0 a b a>0 b>0 = subst (_>𝕂 𝟘) path (·𝕂-Pres>0 (abs𝕂 a) (abs𝕂 b) (abs>0 a a>0) (abs>0 b b>0))
    where
    path : ((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) .fst ≡ a ·𝕂 b
    path = sym (·pos-helper a b (<𝕂→≤𝕂 {a = 𝟘} {b = a} a>0) (<𝕂→≤𝕂 {a = 𝟘} {b = b} b>0))

  trichotomy>𝕂0 : (a : 𝕂) → Trichotomy>0 𝕂CommRing (_>𝕂 𝟘) a
  trichotomy>𝕂0 a = case-split (trichotomy𝕂 a 𝟘)
    where
    case-split : Trichotomy𝕂 a 𝟘 → _
    case-split (lt a<0) = lt (-reverse<0 a a<0)
    case-split (eq a≡0) = eq a≡0
    case-split (gt a>0) = gt a>0


  𝕂OrderedRing : OrderedRing (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  𝕂OrderedRing = 𝕂CommRing ,
    orderstr
      (_>𝕂 𝟘) (λ a → isProp<𝕂 {a = 𝟘} {b = a}) 1>𝕂0
      (λ a → a>0+-a>0→⊥ {a = a}) +𝕂-Pres>0
      ·𝕂'-Pres>0 trichotomy>𝕂0


  {-

    Multiplicative Inverse

  -}
