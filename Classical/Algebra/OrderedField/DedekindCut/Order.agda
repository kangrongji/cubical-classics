{-

Order Structure on Dedekind Cuts

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Algebra.OrderedField.DedekindCut.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Preliminary.Logic
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
  a <𝕂 b = ∥ Σ[ q ∈ K ] ((r : K) → r ∈ b .upper → q < r) × q ∈ a .upper ∥

  _>𝕂_ : 𝕂 → 𝕂 → Type (ℓ-max ℓ ℓ')
  a >𝕂 b = b <𝕂 a

  isProp<𝕂 : {a b : 𝕂} → isProp (a <𝕂 b)
  isProp<𝕂 = squash


  K→𝕂-Pres> : (x y : K) → x < y → (K→𝕂 x) <𝕂 (K→𝕂 y)
  K→𝕂-Pres> x y x<y = ∣ middle x y ,
    (λ q q∈y → <-trans (middle<r x<y) (∈→Inhab (y <P_) q∈y)) ,
    Inhab→∈ (x <P_) (middle>l x<y) ∣

  1>𝕂0 : 𝟙 >𝕂 𝟘
  1>𝕂0 = K→𝕂-Pres> 0r 1r 1>0


  -- Strictness

  <𝕂→≤𝕂 : {a b : 𝕂} → a <𝕂 b → a ≤𝕂 b
  <𝕂→≤𝕂 {a = a} a<b x∈upper = Prop.rec (isProp∈ (a .upper))
    (λ (q , q<r∈upper , q∈upper) → a .upper-close _ _ q∈upper (q<r∈upper _ x∈upper)) a<b

  <𝕂-arefl : {a b : 𝕂} → a <𝕂 b → a ≡ b → ⊥
  <𝕂-arefl {a = a} {b = b} a<b a≡b = Prop.rec isProp⊥
    (λ (q , q<r∈upper , q∈upper) →
      <upper→¬∈upper b _ q<r∈upper (subst (λ x → q ∈ x .upper) a≡b q∈upper)) a<b

  >𝕂-arefl : {a b : 𝕂} → b <𝕂 a → a ≡ b → ⊥
  >𝕂-arefl h p = <𝕂-arefl h (sym p)


  <≤𝕂-asym : (a b : 𝕂) → a <𝕂 b → a ≥𝕂 b → ⊥
  <≤𝕂-asym a b a<b a≥b = <𝕂-arefl {a = a} {b = b} a<b (≤𝕂-asym (<𝕂→≤𝕂 {a = a} {b = b} a<b) a≥b)

  <𝕂-asym : (a b : 𝕂) → a <𝕂 b → a >𝕂 b → ⊥
  <𝕂-asym a b a<b b<a = <≤𝕂-asym a b a<b (<𝕂→≤𝕂 {a = b} {b = a} b<a)


  -- Tons of properties

  ¬a≤b→a>b : (a b : 𝕂) → ¬ (a ≤𝕂 b) → a >𝕂 b
  ¬a≤b→a>b a b ¬a≤b = Prop.map
    (λ (x , ¬x∈upper , x∈upper) → x , ¬∈upper→<upper a x ¬x∈upper , x∈upper)
    (⊈→∃ ¬a≤b)

  open DoubleNegationElim decide

  ¬a>b→a≤b : (a b : 𝕂) → ¬ (a >𝕂 b) → a ≤𝕂 b
  ¬a>b→a≤b a b ¬a>b = ¬¬elim (isProp≤𝕂 {a = a} {b = b}) (¬map (¬a≤b→a>b a b) ¬a>b)

  a≤b→a<b+a≡b : (a b : 𝕂) → a ≤𝕂 b → (a <𝕂 b) ⊎ (a ≡ b)
  a≤b→a<b+a≡b a b a≤b with decide (isProp<𝕂 {a = a} {b = b})
  ... | yes a<b = inl a<b
  ... | no ¬a<b = inr (≤𝕂-asym a≤b (¬a>b→a≤b b a ¬a<b))


  data Trichotomy𝕂 (a b : 𝕂) : Type (ℓ-max ℓ ℓ') where
    gt : a >𝕂 b → Trichotomy𝕂 a b
    eq : a ≡ b  → Trichotomy𝕂 a b
    lt : a <𝕂 b → Trichotomy𝕂 a b

  trichotomy𝕂 : (a b : 𝕂) → Trichotomy𝕂 a b
  trichotomy𝕂 a b with decide (isProp<𝕂 {a = a} {b = b})
  ... | yes a<b = lt a<b
  ... | no ¬a<b =
    case a≤b→a<b+a≡b b a (¬a>b→a≤b b a ¬a<b) of λ
    { (inl b<a) → gt b<a
    ; (inr b≡a) → eq (sym b≡a) }


  data Dichotomy𝕂 (a b : 𝕂) : Type (ℓ-max ℓ ℓ') where
    ge : a ≥𝕂 b → Dichotomy𝕂 a b
    lt : a <𝕂 b → Dichotomy𝕂 a b

  dichotomy𝕂 : (a b : 𝕂) → Dichotomy𝕂 a b
  dichotomy𝕂 a b with decide (isProp<𝕂 {a = a} {b = b})
  ... | yes a<b = lt a<b
  ... | no ¬a<b = ge (¬a>b→a≤b b a ¬a<b)


  data Split≤𝕂 (a b : 𝕂)(a≤b : a ≤𝕂 b) : Type (ℓ-max ℓ ℓ') where
    lt : a <𝕂 b → Split≤𝕂 a b a≤b
    eq : a ≡ b  → Split≤𝕂 a b a≤b

  split≤𝕂 : (a b : 𝕂) → (a≤b : a ≤𝕂 b) → Split≤𝕂 a b a≤b
  split≤𝕂 a b a≤b with dichotomy𝕂 a b
  ... | lt a<b = lt a<b
  ... | ge a≥b = eq (≤𝕂-asym a≤b a≥b)


  +𝕂-Pres< : (a b c d : 𝕂) → a <𝕂 b → c <𝕂 d → (a +𝕂 c) <𝕂 (b +𝕂 d)
  +𝕂-Pres< a b c d a<b b<c = Prop.map2
    (λ (q , q<b∈upper , q∈aupper) (p , p<d∈upper , p∈cupper) →
      q + p ,
      (λ x x∈b+d → Prop.rec isProp<
        (λ (s , t , s∈b , t∈d , x≡s+t) →
          subst (q + p <_) (sym x≡s+t) (+-Pres< (q<b∈upper s s∈b) (p<d∈upper t t∈d)))
        (∈→Inhab (+upper b d) x∈b+d)) ,
      Inhab→∈ (+upper a c) ∣ q , p , q∈aupper , p∈cupper , refl ∣ )
    a<b b<c

  +𝕂-Pres≤ : (a b c d : 𝕂) → a ≤𝕂 b → c ≤𝕂 d → (a +𝕂 c) ≤𝕂 (b +𝕂 d)
  +𝕂-Pres≤ a b c d a≤b c≤d x∈b+d =
    Prop.rec (isProp∈ ((a +𝕂 c) .upper))
    (λ (s , t , s∈b , t∈d , x≡s+t) →
      Inhab→∈ (+upper a c) ∣ s , t , a≤b s∈b , c≤d t∈d , x≡s+t ∣)
    (∈→Inhab (+upper b d) x∈b+d)

  +𝕂-rPres≤ : (a b c : 𝕂) → a ≤𝕂 b → (a +𝕂 c) ≤𝕂 (b +𝕂 c)
  +𝕂-rPres≤ a b c a≤b = +𝕂-Pres≤ a b c c a≤b (≤𝕂-refl {a = c} refl)

  private
    alg-helper'' : (a c : 𝕂) → (a +𝕂 c) +𝕂 (-𝕂 c) ≡ a
    alg-helper'' a c = sym (+𝕂-Assoc _ _ _) ∙ (λ i → a +𝕂 +𝕂-rInverse c i) ∙ +𝕂-rUnit a

    alg-helper''' : (a b c : 𝕂) → (a +𝕂 b) +𝕂 c ≡ (a +𝕂 c) +𝕂 b
    alg-helper''' a b c = sym (+𝕂-Assoc _ _ _) ∙ (λ i → a +𝕂 +𝕂-Comm b c i) ∙ +𝕂-Assoc _ _ _

  +𝕂-rPres≤- : (a b c : 𝕂) → (a +𝕂 c) ≤𝕂 (b +𝕂 c) → a ≤𝕂 b
  +𝕂-rPres≤- a b c a+c≤b+c = transport (λ i → alg-helper'' a c i ≤𝕂 alg-helper'' b c i)
    (+𝕂-rPres≤ (a +𝕂 c) (b +𝕂 c) (-𝕂 c) a+c≤b+c)

  +𝕂-rPres< : (a b c : 𝕂) → a <𝕂 b → (a +𝕂 c) <𝕂 (b +𝕂 c)
  +𝕂-rPres< a b c a<b = ¬a≤b→a>b (b +𝕂 c) (a +𝕂 c) (¬map (+𝕂-rPres≤- b a c) (<≤𝕂-asym a b a<b))


  <𝕂-reverse' : (a b : 𝕂) → a <𝕂 b → (-𝕂 b) <𝕂 (-𝕂 a)
  <𝕂-reverse' a b a<b = transport (λ i → path1 i <𝕂 path2 i)
    (+𝕂-rPres< (a +𝕂 (-𝕂 a)) (b +𝕂 (-𝕂 a)) (-𝕂 b) (+𝕂-rPres< a b (-𝕂 a) a<b))
    where
    path1 : (a +𝕂 (-𝕂 a)) +𝕂 (-𝕂 b) ≡ (-𝕂 b)
    path1 = (λ i → +𝕂-rInverse a i +𝕂 (-𝕂 b)) ∙ +𝕂-lUnit (-𝕂 b)
    path2 : (b +𝕂 (-𝕂 a)) +𝕂 (-𝕂 b) ≡ (-𝕂 a)
    path2 = alg-helper''' _ _ _ ∙ (λ i → +𝕂-rInverse b i +𝕂 (-𝕂 a)) ∙ +𝕂-lUnit (-𝕂 a)

  <𝕂-reverse : (a b : 𝕂) → a <𝕂 b → (-𝕂 b) ≤𝕂 (-𝕂 a)
  <𝕂-reverse a b a<b = <𝕂→≤𝕂 {a = (-𝕂 b)} {b = (-𝕂 a)} (<𝕂-reverse' a b a<b)

  -0≡0 : -𝕂 𝟘 ≡ 𝟘
  -0≡0 = sym (+𝕂-rUnit (-𝕂 𝟘)) ∙ +𝕂-lInverse 𝟘

  -reverse>0 : (a : 𝕂) → a >𝕂 𝟘 → (-𝕂 a) <𝕂 𝟘
  -reverse>0 a a>0 = subst ((-𝕂 a) <𝕂_) -0≡0 (<𝕂-reverse' 𝟘 a a>0)

  -reverse<0 : (a : 𝕂) → a <𝕂 𝟘 → (-𝕂 a) >𝕂 𝟘
  -reverse<0 a a<0 = subst (_<𝕂 (-𝕂 a)) -0≡0 (<𝕂-reverse' a 𝟘 a<0)

  <0-reverse : (a : 𝕂) → a <𝕂 𝟘 → (-𝕂 a) ≥𝕂 𝟘
  <0-reverse a a<0 = <𝕂→≤𝕂 {a = 𝟘} {b = (-𝕂 a)} (-reverse<0 a a<0)


  +𝕂-Pres<0 : (a b : 𝕂) → a <𝕂 𝟘 → b <𝕂 𝟘 → (a +𝕂 b) <𝕂 𝟘
  +𝕂-Pres<0 a b a<0 b<0 = subst ((a +𝕂 b) <𝕂_) (+𝕂-rUnit 𝟘) (+𝕂-Pres< a 𝟘 b 𝟘 a<0 b<0)

  +𝕂-Pres≥0 : (a b : 𝕂) → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → (a +𝕂 b) ≥𝕂 𝟘
  +𝕂-Pres≥0 a b a≥0 b≥0 = subst ((a +𝕂 b) ≥𝕂_) (+𝕂-rUnit 𝟘) (+𝕂-Pres≤ 𝟘 a 𝟘 b a≥0 b≥0)

  +𝕂-Pres>0 : (a b : 𝕂) → a >𝕂 𝟘 → b >𝕂 𝟘 → (a +𝕂 b) >𝕂 𝟘
  +𝕂-Pres>0 a b a>0 b>0 = subst ((a +𝕂 b) >𝕂_) (+𝕂-rUnit 𝟘) (+𝕂-Pres< 𝟘 a 𝟘 b a>0 b>0)


  ·𝕂-Pres>0 : (a b : 𝕂₊) → a .fst >𝕂 𝟘 → b .fst >𝕂 𝟘 → (a ·𝕂₊ b) .fst >𝕂 𝟘
  ·𝕂-Pres>0 a b a>0 b>0 = Prop.map2
    (λ (q , q<r∈a , q∈𝟘) (p , p<r∈b , p∈𝟘) →
      let q>0 = q∈𝕂₊→q>0 𝟘₊ q q∈𝟘
          p>0 = q∈𝕂₊→q>0 𝟘₊ p p∈𝟘 in
      q · p ,
      (λ x x∈a·b → Prop.rec isProp<
        (λ (s , t , s∈a , t∈b , x≡s·t) →
          subst (q · p <_) (sym x≡s·t)
            (·-PosPres> q>0 p>0 (q<r∈a s s∈a) (p<r∈b t t∈b)))
        (∈→Inhab (·upper₊ a b) x∈a·b)) ,
      Inhab→∈ (0r <P_) (·-Pres>0 q>0 p>0) )
    a>0 b>0


  -- Two lemmas for convenient case-splitting

  a≥0+-a≥0→a≡0 : {a : 𝕂} → a ≥𝕂 𝟘 → (-𝕂 a) ≥𝕂 𝟘 → a ≡ 𝟘
  a≥0+-a≥0→a≡0 {a = a} a≥0 -a≥0 with split≤𝕂 𝟘 a a≥0
  ... | lt 0<a = Empty.rec (<≤𝕂-asym (-𝕂 a) 𝟘 (-reverse>0 a 0<a) -a≥0)
  ... | eq 0≡a = sym 0≡a

  a<0+-a<0→⊥ : {a : 𝕂} → a <𝕂 𝟘 → (-𝕂 a) <𝕂 𝟘 → ⊥
  a<0+-a<0→⊥ {a = a} a<0 -a<0 = <𝕂-asym (-𝕂 a) 𝟘 -a<0 (-reverse<0 a a<0)

  a>0+-a>0→⊥ : {a : 𝕂} → a >𝕂 𝟘 → (-𝕂 a) >𝕂 𝟘 → ⊥
  a>0+-a>0→⊥ {a = a} a>0 -a>0 = <𝕂-asym 𝟘 (-𝕂 a) -a>0 (-reverse>0 a a>0)


  {-

    Absolute Value

  -}

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

    Signature

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
