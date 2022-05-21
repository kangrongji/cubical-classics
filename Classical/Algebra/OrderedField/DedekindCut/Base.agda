{-

The Dedekind Cut

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.DedekindCut.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection

open import Classical.Axioms
open import Classical.Foundations.Powerset
open import Classical.Algebra.OrderedField

private
  variable
    ℓ ℓ' : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (a b c d : 𝓡 .fst) → c + ((a + b) - d) ≡ a + (b + (c - d))
    helper1 = solve 𝓡

    helper2 : (c d : 𝓡 .fst) → c ≡ c + (d - d)
    helper2 = solve 𝓡

    helper1' : (a b c d : 𝓡 .fst) → c · ((a · b) · d) ≡ a · (b · (c · d))
    helper1' = solve 𝓡


module Basics ⦃ 🤖 : Oracle ⦄
  (𝒦 : OrderedField ℓ ℓ')
  where

  open Oracle 🤖

  private
    K = 𝒦 .fst .fst .fst


  open OrderedFieldStr 𝒦

  open Helpers (𝒦 .fst .fst)


  {-

    Dedekind Cut

  -}

  record DedekindCut : Type (ℓ-max ℓ ℓ') where
    no-eta-equality

    field

      upper : ℙ K
      upper-inhab : ∥ Σ[ q ∈ K ] q ∈ upper ∥
      upper-close : (r : K)(q : K) → q ∈ upper → q < r → r ∈ upper
      upper-round : (q : K) → q ∈ upper → ∥ Σ[ r ∈ K ] (r < q) × (r ∈ upper) ∥
      lower-inhab : ∥ Σ[ q ∈ K ] ((r : K) → r ∈ upper → q < r) ∥


  open DedekindCut


  -- Dedekind Completion of K

  𝕂 : Type (ℓ-max ℓ ℓ')
  𝕂 = DedekindCut


  {-

    hLevel of 𝕂

  -}

  -- Construct path in 𝕂 from path of two cuts

  path-𝕂 : (a b : DedekindCut) → a .upper ≡ b .upper → a ≡ b
  path-𝕂 a b upper-path i .upper = upper-path i
  path-𝕂 a b upper-path i .upper-inhab =
    isProp→PathP (λ i → squash {A = Σ[ q ∈ K ] q ∈ upper-path i}) (a .upper-inhab) (b .upper-inhab) i
  path-𝕂 a b upper-path i .upper-close =
    isProp→PathP (λ i → isPropΠ4 {C = λ _ q → q ∈ upper-path i} (λ _ _ _ _ → isProp∈ (upper-path i)))
    (a .upper-close) (b .upper-close) i
  path-𝕂 a b upper-path i .upper-round =
    isProp→PathP (λ i → isPropΠ2 {B = λ q → q ∈ upper-path i}
      (λ q _ → squash {A = Σ[ r ∈ K ] (r < q) × (r ∈ upper-path i)}))
    (a .upper-round) (b .upper-round) i
  path-𝕂 a b upper-path i .lower-inhab =
    isProp→PathP (λ i → squash {A = Σ[ q ∈ K ] ((r : K) → r ∈ upper-path i → q < r)})
    (a .lower-inhab) (b .lower-inhab) i

  -- 𝕂 is hSet

  isSet𝕂 : isSet 𝕂
  isSet𝕂 a b p q i j =
    hcomp (λ k → λ
      { (i = i0) → path-𝕂 (lift-square i0 j) (p j) refl k
      ; (i = i1) → path-𝕂 (lift-square i1 j) (q j) refl k
      ; (j = i0) → path-𝕂 a a refl k
      ; (j = i1) → path-𝕂 b b refl k })
    (lift-square i j)
    where
    lift-square : (i j : I) → 𝕂
    lift-square i j = path-𝕂 a b
      (isSet→SquareP (λ _ _ → isSetℙ {X = K}) (cong upper p) (cong upper q) refl refl i) j


  {-

    Inclusion of K into 𝕂

  -}

  -- Rational number is real number

  _<P_ : K → K → hProp ℓ'
  _<P_ p q = (p < q) , isProp<

  K→𝕂 : K → 𝕂
  K→𝕂 q .upper = specify (q <P_)
  K→𝕂 q .upper-inhab = ∣ q + 1r , Inhab→∈ (q <P_) q+1>q ∣
  K→𝕂 q .upper-close r s s∈upper r>s = Inhab→∈ (q <P_) (<-trans (∈→Inhab (q <P_) s∈upper) r>s)
  K→𝕂 q .upper-round r r∈upper = ∣ middle q r , middle<r {p = q} {q = r} r>q , Inhab→∈ (q <P_) (middle>l r>q) ∣
    where r>q : r > q
          r>q = ∈→Inhab (q <P_) r∈upper
  K→𝕂 q .lower-inhab = ∣ q - 1r , (λ r r∈upper → <-trans q-1<q (∈→Inhab (q <P_) r∈upper)) ∣


  -- Zero and Unit

  𝟘 : 𝕂
  𝟘 = K→𝕂 0r

  𝟙 : 𝕂
  𝟙 = K→𝕂 1r


  {-

    The natural order on 𝕂

  -}

  _≤𝕂_ : 𝕂 → 𝕂 → Type ℓ
  a ≤𝕂 b = b .upper ⊆ a .upper

  _≥𝕂_ : 𝕂 → 𝕂 → Type ℓ
  a ≥𝕂 b = b ≤𝕂 a

  isProp≤𝕂 : {a b : 𝕂} → isProp (a ≤𝕂 b)
  isProp≤𝕂 = isProp⊆

  ≤𝕂-refl : {a b : 𝕂} → a ≡ b → a ≤𝕂 b
  ≤𝕂-refl a≡b {x = q} q∈upper = subst (λ p → q ∈ p .upper) (sym a≡b) q∈upper

  ≤𝕂-asym : {a b : 𝕂} → a ≤𝕂 b → b ≤𝕂 a → a ≡ b
  ≤𝕂-asym a≤b b≤a = path-𝕂 _ _ (bi⊆→≡ b≤a a≤b)


  {-

    Non-membership of upper cut

  -}

  module _ (a : 𝕂)(q : K) where

    ¬∈upper→<upper : ¬ q ∈ a .upper → (r : K) → r ∈ a .upper → q < r
    ¬∈upper→<upper ¬q∈upper r r∈upper = case-split (trichotomy q r)
      where
      case-split : Trichotomy q r → q < r
      case-split (lt q<r) = q<r
      case-split (eq q≡r) = Empty.rec (¬q∈upper (subst (_∈ a .upper) (sym q≡r) r∈upper))
      case-split (gt q>r) = Empty.rec (¬q∈upper (a .upper-close _ _ r∈upper q>r))

    <upper→¬∈upper : ((r : K) → r ∈ a .upper → q < r) → ¬ q ∈ a .upper
    <upper→¬∈upper q<r∈upper = case-split (decide (isProp∈ (a .upper)))
      where
      case-split : Dec (q ∈ a .upper) → ¬ q ∈ a .upper
      case-split (yes p) _ = <-arefl (q<r∈upper q p) refl
      case-split (no ¬p) = ¬p


  ¬∈upper-close : (a : 𝕂)(p q : K) → ¬ q ∈ a .upper → p < q → ¬ p ∈ a .upper
  ¬∈upper-close a p q ¬q∈upper p<q =
    <upper→¬∈upper a _ (λ r r∈upper → <-trans p<q (¬∈upper→<upper a _ ¬q∈upper r r∈upper))


  {-

    Basic algebraic operations of 𝕂

  -}


  -- Additive Inverse

  -upper : (a : 𝕂)(x : K) → hProp (ℓ-max ℓ ℓ')
  -upper a x = ∥ Σ[ p ∈ K ] ((r : K) → r ∈ a .upper → p < r) × (x > - p) ∥ , squash

  -𝕂_ : 𝕂 → 𝕂
  (-𝕂 a) .upper = specify (-upper a)
  (-𝕂 a) .upper-inhab = Prop.map
    (λ (q , q<r∈upper) →
      (- q) + 1r , Inhab→∈ (-upper a) ∣ q , q<r∈upper , q+1>q ∣ )
    (a .lower-inhab)
  (-𝕂 a) .upper-close r q q∈upper q<r = Prop.rec (isProp∈ ((-𝕂 a) .upper))
    (λ (p , p<r∈upper , q>-p) →
      Inhab→∈ (-upper a) ∣ p , p<r∈upper , <-trans q>-p q<r ∣)
    (∈→Inhab (-upper a) q∈upper)
  (-𝕂 a) .upper-round q q∈upper = Prop.map
    (λ (p , p<r∈upper , q>-p) →
      middle (- p) q , middle<r q>-p  , Inhab→∈ (-upper a) ∣ p , p<r∈upper , middle>l q>-p ∣)
    (∈→Inhab (-upper a) q∈upper)
  (-𝕂 a) .lower-inhab = Prop.map
    (λ (q , q∈upper) →
      - q , λ r r∈upper → Prop.rec isProp<
        (λ (p , p<s∈upper , r>-p) →
          <-trans (-Reverse< (p<s∈upper q q∈upper)) r>-p)
        (∈→Inhab (-upper a) r∈upper))
    (a .upper-inhab)


  -- Addition

  +upper : 𝕂 → 𝕂 → K → hProp ℓ
  +upper a b r = ∥ Σ[ p ∈ K ] Σ[ q ∈ K ] p ∈ a .upper × q ∈ b .upper × (r ≡ p + q) ∥ , squash

  private
    alg-helper : (a b c d : K) → d ≡ a + b → c ≡ a + (b + (c - d))
    alg-helper a b c d d≡a+b = helper2 c d ∙ (λ i → c + (d≡a+b i - d)) ∙ helper1 a b c d

  _+𝕂_ : 𝕂 → 𝕂 → 𝕂
  (a +𝕂 b) .upper = specify (+upper a b)
  (a +𝕂 b) .upper-inhab = Prop.map2
    (λ (p , p∈upper) (q , q∈upper) →
      p + q , Inhab→∈ (+upper a b) ∣ p , q , p∈upper , q∈upper , refl ∣)
    (a .upper-inhab) (b .upper-inhab)
  (a +𝕂 b) .upper-close r q q∈upper q<r = Prop.rec (isProp∈ ((a +𝕂 b) .upper))
    (λ (s , t , s∈upper , t∈upper , q≡s+t) →
      let t+r-q∈upper : (t + (r - q)) ∈ b .upper
          t+r-q∈upper = b .upper-close _ _ t∈upper (+-rPos→> (>→Diff>0 q<r))
          r≡s+t+r-q : r ≡ s + (t + (r - q))
          r≡s+t+r-q = alg-helper s t r q q≡s+t
      in  Inhab→∈ (+upper a b) ∣ s , t + (r - q) , s∈upper , t+r-q∈upper , r≡s+t+r-q ∣)
    (∈→Inhab (+upper a b) q∈upper)
  (a +𝕂 b) .upper-round q q∈upper = Prop.rec squash
    (λ (s , t , s∈upper , t∈upper , q≡s+t) → Prop.map2
      (λ (s' , s'<s , s'∈upper) (t' , t'<t , t'∈upper) →
        s' + t' , subst (s' + t' <_) (sym q≡s+t) (+-Pres< s'<s t'<t) ,
        Inhab→∈ (+upper a b) ∣ s' , t' , s'∈upper , t'∈upper , refl ∣)
      (a .upper-round s s∈upper) (b .upper-round t t∈upper))
    (∈→Inhab (+upper a b) q∈upper)
  (a +𝕂 b) .lower-inhab = Prop.map2
    (λ (p , p<r∈upper) (q , q<r∈upper) →
        p + q , λ r r∈upper → Prop.rec isProp<
          (λ (s , t , s∈upper , t∈upper , r≡s+t) →
            subst (p + q <_) (sym r≡s+t)
            (+-Pres< (p<r∈upper s s∈upper) (q<r∈upper t t∈upper)))
          (∈→Inhab (+upper a b) r∈upper))
    (a .lower-inhab) (b .lower-inhab)


  {-

    Non-Negative Reals

  -}

  𝕂₊ : Type (ℓ-max ℓ ℓ')
  𝕂₊ = Σ[ r ∈ 𝕂 ] (r ≥𝕂 𝟘)

  path-𝕂₊ : (a b : 𝕂₊) → a .fst ≡ b .fst → a ≡ b
  path-𝕂₊ a b p i .fst = p i
  path-𝕂₊ a b p i .snd = isProp→PathP (λ i → isProp≤𝕂 {a = 𝟘} {b = p i}) (a .snd) (b .snd) i

  q∈𝕂₊→q>0 : (a : 𝕂₊)(q : K) → q ∈ a .fst .upper → q > 0r
  q∈𝕂₊→q>0 a q q∈upper = ∈→Inhab (0r <P_) (a .snd q∈upper)


  -- Zero and Unit

  𝟘₊ : 𝕂₊
  𝟘₊ = 𝟘 , ≡→⊆ {A = 𝟘 .upper} refl

  𝟙₊ : 𝕂₊
  𝟙₊ = 𝟙 , λ q∈upper → Inhab→∈ (0r <P_) (<-trans 1>0 (∈→Inhab (1r <P_) q∈upper))


  -- Addition

  +upper₊ : 𝕂₊ → 𝕂₊ → K → hProp ℓ
  +upper₊ a b = +upper (a .fst) (b .fst)

  _+𝕂₊_ : (a b : 𝕂₊) → 𝕂₊
  ((a , a≥0) +𝕂₊ (b , b≥0)) .fst = a +𝕂 b
  ((a , a≥0) +𝕂₊ (b , b≥0)) .snd q∈upper =
    Prop.rec (isProp∈ (𝟘 .upper))
    (λ (s , t , s∈upper , t∈upper , q≡s+t) →
      let s>0 = ∈→Inhab (0r <P_) (a≥0 s∈upper)
          t>0 = ∈→Inhab (0r <P_) (b≥0 t∈upper)
      in  Inhab→∈ (0r <P_) (subst (_> 0r) (sym q≡s+t) (+-Pres>0 s>0 t>0)))
    (∈→Inhab (+upper a b) q∈upper)


  -- Multiplication

  ·upper : 𝕂 → 𝕂 → K → hProp ℓ
  ·upper a b r = ∥ Σ[ p ∈ K ] Σ[ q ∈ K ] p ∈ a .upper × q ∈ b .upper × (r ≡ p · q) ∥ , squash

  ·upper₊ : 𝕂₊ → 𝕂₊ → K → hProp ℓ
  ·upper₊ a b = ·upper (a .fst) (b .fst)


  ≥𝕂0+q∈upper→q>0 : (a : 𝕂){q : K} → a ≥𝕂 𝟘 → q ∈ a .upper → q > 0r
  ≥𝕂0+q∈upper→q>0 a {q = q} a≥0 q∈upper = ∈→Inhab (0r <P_) (a≥0 q∈upper)

  q∈·upper→q>0 : (a b : 𝕂) → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → (q : K) → q ∈ specify (·upper a b) → q > 0r
  q∈·upper→q>0 a b a≥0 b≥0 q q∈upper = Prop.rec isProp<
    (λ (s , t , s∈upper , t∈upper , q≡s·t) →
      subst (_> 0r) (sym q≡s·t)
        (·-Pres>0 (≥𝕂0+q∈upper→q>0 a a≥0 s∈upper) (≥𝕂0+q∈upper→q>0 b b≥0 t∈upper)))
    (∈→Inhab (·upper a b) q∈upper)

  private
    alg-helper' : (a b c d : K)(d≢0 : ¬ d ≡ 0r) → d ≡ a · b → c ≡ a · (b · (c · inv d≢0))
    alg-helper' a b c d d≢0 d≡a·b =
        sym (·Rid c) ∙ (λ i → c · ·-rInv d≢0 (~ i))
      ∙ (λ i → c · (d≡a·b i · inv d≢0)) ∙ helper1' a b c (inv d≢0)

  _·𝕂₊_ : (a b : 𝕂₊) → 𝕂₊
  ((a , a≥0) ·𝕂₊ (b , b≥0)) .fst .upper = specify (·upper a b)
  ((a , a≥0) ·𝕂₊ (b , b≥0)) .fst .upper-inhab = Prop.map2
    (λ (p , p∈upper) (q , q∈upper) →
      p · q , Inhab→∈ (·upper a b) ∣ p , q , p∈upper , q∈upper , refl ∣)
    (a .upper-inhab) (b .upper-inhab)
  ((a , a≥0) ·𝕂₊ (b , b≥0)) .fst .upper-close r q q∈upper q<r =
    Prop.rec (isProp∈ (((a , a≥0) ·𝕂₊ (b , b≥0)) .fst .upper))
    (λ (s , t , s∈upper , t∈upper , q≡s·t) →
      let q>0 : q > 0r
          q>0 = q∈·upper→q>0 a b a≥0 b≥0 q q∈upper
          q≢0 : ¬ q ≡ 0r
          q≢0 = >-arefl q>0
          q⁻¹ = inv q≢0
          t·r·q⁻¹∈upper : (t · (r · q⁻¹)) ∈ b .upper
          t·r·q⁻¹∈upper = b .upper-close _ _ t∈upper
            (·-Pos·>1→> (≥𝕂0+q∈upper→q>0 b b≥0 t∈upper) (p>q>0→p·q⁻¹>1 q>0 q<r))
          r≡s·t·r·q⁻¹ : r ≡ s · (t · (r · q⁻¹))
          r≡s·t·r·q⁻¹ = alg-helper' s t r q q≢0 q≡s·t
      in  Inhab→∈ (·upper a b) ∣ s , t · (r · q⁻¹) , s∈upper , t·r·q⁻¹∈upper , r≡s·t·r·q⁻¹ ∣)
    (∈→Inhab (·upper a b) q∈upper)
  ((a , a≥0) ·𝕂₊ (b , b≥0)) .fst .upper-round q q∈upper = Prop.rec squash
    (λ (s , t , s∈upper , t∈upper , q≡s·t) → Prop.map2
      (λ (s' , s'<s , s'∈upper) (t' , t'<t , t'∈upper) →
        s' · t' , subst (s' · t' <_) (sym q≡s·t)
          (·-PosPres> (≥𝕂0+q∈upper→q>0 a a≥0 s'∈upper) (≥𝕂0+q∈upper→q>0 b b≥0 t'∈upper) s'<s t'<t) ,
        Inhab→∈ (·upper a b) ∣ s' , t' , s'∈upper , t'∈upper , refl ∣ )
      (a .upper-round s s∈upper) (b .upper-round t t∈upper))
    (∈→Inhab (·upper a b) q∈upper)
  ((a , a≥0) ·𝕂₊ (b , b≥0)) .fst .lower-inhab =
    ∣ - 1r , (λ r r∈upper → <-trans -1<0 (q∈·upper→q>0 a b a≥0 b≥0 r r∈upper)) ∣
  ((a , a≥0) ·𝕂₊ (b , b≥0)) .snd q∈upper =
    Prop.rec (isProp∈ (𝟘 .upper))
    (λ (s , t , s∈upper , t∈upper , q≡s·t) →
      let s>0 = ∈→Inhab (0r <P_) (a≥0 s∈upper)
          t>0 = ∈→Inhab (0r <P_) (b≥0 t∈upper)
      in  Inhab→∈ (0r <P_) (subst (_> 0r) (sym q≡s·t) (·-Pres>0 s>0 t>0)))
    (∈→Inhab (·upper a b) q∈upper)


  -- Multiplicative Inverse

  inv-upper : (a : 𝕂)(x : K) → hProp (ℓ-max ℓ ℓ')
  inv-upper a x = ∥ Σ[ p ∈ K ] Σ[ p>0 ∈ p > 0r ] ((r : K) → r ∈ a .upper → p < r) × (x > inv (>-arefl p>0)) ∥ , squash

  inv𝕂₊ : (a : 𝕂)(q : K) → q > 0r → ((r : K) → r ∈ a .upper → q < r) → 𝕂₊
  inv𝕂₊ a _ _ _ .fst .upper = specify (inv-upper a)
  inv𝕂₊ a q₀ q₀>0 q₀<r∈upper .fst .upper-inhab =
    let q₀⁻¹ = inv (>-arefl q₀>0) in
    ∣ q₀⁻¹ + 1r , Inhab→∈ (inv-upper a) ∣ q₀ , q₀>0 , q₀<r∈upper , q+1>q {q = q₀⁻¹} ∣ ∣
  inv𝕂₊ a q₀ q₀>0 q₀<r∈upper .fst .upper-close r q q∈upper q<r =
    Prop.rec (isProp∈ (inv𝕂₊ a q₀ q₀>0 q₀<r∈upper .fst .upper))
    (λ (p , p>0 , p<r∈upper , q>p⁻¹) →
      Inhab→∈ (inv-upper a) ∣ p , p>0 , p<r∈upper , <-trans q>p⁻¹ q<r ∣)
    (∈→Inhab (inv-upper a) q∈upper)
  inv𝕂₊ a _ _ _ .fst .upper-round q q∈upper = Prop.map
    (λ (p , p>0 , p<r∈upper , q>p⁻¹) →
      let p⁻¹ = inv (>-arefl p>0) in
      middle p⁻¹ q , middle<r q>p⁻¹  , Inhab→∈ (inv-upper a) ∣ p , p>0 , p<r∈upper , middle>l q>p⁻¹ ∣)
    (∈→Inhab (inv-upper a) q∈upper)
  inv𝕂₊ a q₀ q₀>0 q₀<r∈upper .fst .lower-inhab = Prop.map
    (λ (q , q∈upper) →
      let q>0 = <-trans q₀>0 (q₀<r∈upper q q∈upper)
          q⁻¹ = inv (>-arefl q>0) in
      q⁻¹ , λ r r∈upper → Prop.rec isProp<
        (λ (p , p>0 , p<s∈upper , r>p⁻¹) →
          <-trans (inv-Reverse< _ _ (p<s∈upper q q∈upper)) r>p⁻¹)
        (∈→Inhab (inv-upper a) r∈upper))
    (a .upper-inhab)
  inv𝕂₊ a _ _ _ .snd q∈upper =
    Prop.rec (isProp∈ (𝟘 .upper))
    (λ (p , p>0 , p<r∈upper , q>p⁻¹) →
      Inhab→∈ (0r <P_) (<-trans (p>0→p⁻¹>0 p>0) q>p⁻¹))
    (∈→Inhab (inv-upper a) q∈upper)
