{-

The Dedekind Cut

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Analysis.Real.Base.DedekindCut where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (a b c d : 𝓡 .fst) → c + ((a + b) - d) ≡ a + (b + (c - d))
    helper1 = solve 𝓡

    helper2 : (c d : 𝓡 .fst) → c ≡ c + (d - d)
    helper2 = solve 𝓡

    helper1' : (a b c d : 𝓡 .fst) → c · ((a · b) · d) ≡ a · (b · (c · d))
    helper1' = solve 𝓡


open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Literals public
open import Cubical.HITs.Rationals.QuoQ using (ℚ)
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Preliminary.QuoQ
open import Classical.Algebra.OrderedField
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset


open Helpers (ℚOrderedField .fst .fst)


module Basics (decide : LEM) where

  open Powerset decide

  open OrderedFieldStr ℚOrderedField


  {-

    Dedekind Cut

  -}

  record DedekindCut : Type where
    no-eta-equality

    field

      upper : ℙ ℚ
      upper-inhab : ∥ Σ[ q ∈ ℚ ] q ∈ upper ∥
      upper-close : (r : ℚ)(q : ℚ) → q ∈ upper → q < r → r ∈ upper
      upper-round : (q : ℚ) → q ∈ upper → ∥ Σ[ r ∈ ℚ ] (r < q) × (r ∈ upper) ∥
      lower-inhab : ∥ Σ[ q ∈ ℚ ] ((r : ℚ) → r ∈ upper → q < r) ∥


  open DedekindCut


  -- Dedekind Real Number

  ℝ : Type
  ℝ = DedekindCut


  {-

    hLevel of ℝ

  -}

  -- Construct path in ℝ from path of two cuts

  path-ℝ : (a b : DedekindCut) → a .upper ≡ b .upper → a ≡ b
  path-ℝ a b upper-path i .upper = upper-path i
  path-ℝ a b upper-path i .upper-inhab =
    isProp→PathP (λ i → squash {A = Σ[ q ∈ ℚ ] q ∈ upper-path i}) (a .upper-inhab) (b .upper-inhab) i
  path-ℝ a b upper-path i .upper-close =
    isProp→PathP (λ i → isPropΠ4 {C = λ _ q → q ∈ upper-path i} (λ _ _ _ _ → isProp∈ (upper-path i)))
    (a .upper-close) (b .upper-close) i
  path-ℝ a b upper-path i .upper-round =
    isProp→PathP (λ i → isPropΠ2 {B = λ q → q ∈ upper-path i}
      (λ q _ → squash {A = Σ[ r ∈ ℚ ] (r < q) × (r ∈ upper-path i)}))
    (a .upper-round) (b .upper-round) i
  path-ℝ a b upper-path i .lower-inhab =
    isProp→PathP (λ i → squash {A = Σ[ q ∈ ℚ ] ((r : ℚ) → r ∈ upper-path i → q < r)})
    (a .lower-inhab) (b .lower-inhab) i

  -- ℝ is hSet

  isSetℝ : isSet ℝ
  isSetℝ a b p q i j =
    hcomp (λ k → λ
      { (i = i0) → path-ℝ (lift-square i0 j) (p j) refl k
      ; (i = i1) → path-ℝ (lift-square i1 j) (q j) refl k
      ; (j = i0) → path-ℝ a a refl k
      ; (j = i1) → path-ℝ b b refl k })
    (lift-square i j)
    where
    lift-square : (i j : I) → ℝ
    lift-square i j = path-ℝ a b
      (isSet→SquareP (λ _ _ → isSetℙ {X = ℚ}) (cong upper p) (cong upper q) refl refl i) j


  {-

    Inclusion of ℚ into ℝ

  -}

  -- Rational number is real number

  _<P_ : ℚ → ℚ → hProp ℓ-zero
  _<P_ p q = (p < q) , isProp<

  ℚ→ℝ : ℚ → ℝ
  ℚ→ℝ q .upper = specify (q <P_)
  ℚ→ℝ q .upper-inhab = ∣ q + 1 , Inhab→∈ (q <P_) q+1>q ∣
  ℚ→ℝ q .upper-close r s s∈upper r>s = Inhab→∈ (q <P_) (<-trans (∈→Inhab (q <P_) s∈upper) r>s)
  ℚ→ℝ q .upper-round r r∈upper = ∣ middle q r , middle<r {p = q} {q = r} r>q , Inhab→∈ (q <P_) (middle>l r>q) ∣
    where r>q : r > q
          r>q = ∈→Inhab (q <P_) r∈upper
  ℚ→ℝ q .lower-inhab = ∣ q - 1 , (λ r r∈upper → <-trans q-1<q (∈→Inhab (q <P_) r∈upper)) ∣


  -- Positive and negative integer literals for ℝ

  instance
    fromNatℝ : HasFromNat ℝ
    fromNatℝ = record { Constraint = λ _ → Unit ; fromNat = λ n → ℚ→ℝ (ℕ→ℚPos n) }

  instance
    fromNegℝ : HasFromNeg ℝ
    fromNegℝ = record { Constraint = λ _ → Unit ; fromNeg = λ n → ℚ→ℝ (ℕ→ℚNeg n) }


  {-

    The natural order on ℝ

  -}

  _≤ℝ_ : ℝ → ℝ → Type
  a ≤ℝ b = b .upper ⊆ a .upper

  _≥ℝ_ : ℝ → ℝ → Type
  a ≥ℝ b = b ≤ℝ a

  isProp≤ℝ : {a b : ℝ} → isProp (a ≤ℝ b)
  isProp≤ℝ = isProp⊆

  ≤ℝ-asym : {a b : ℝ} → a ≤ℝ b → b ≤ℝ a → a ≡ b
  ≤ℝ-asym a≤b b≤a = path-ℝ _ _ (bi⊆→≡ b≤a a≤b)


  {-

    Non-membership of upper cut

  -}

  module _ (a : ℝ)(q : ℚ) where

    ¬∈upper→<upper : ¬ q ∈ a .upper → (r : ℚ) → r ∈ a .upper → q < r
    ¬∈upper→<upper ¬q∈upper r r∈upper = case-split (trichotomy q r)
      where
      case-split : Trichotomy q r → q < r
      case-split (lt q<r) = q<r
      case-split (eq q≡r) = Empty.rec (¬q∈upper (subst (_∈ a .upper) (sym q≡r) r∈upper))
      case-split (gt q>r) = Empty.rec (¬q∈upper (a .upper-close _ _ r∈upper q>r))

    <upper→¬∈upper : ((r : ℚ) → r ∈ a .upper → q < r) → ¬ q ∈ a .upper
    <upper→¬∈upper q<r∈upper = case-split (decide (isProp∈ (a .upper)))
      where
      case-split : Dec (q ∈ a .upper) → ¬ q ∈ a .upper
      case-split (yes p) _ = <-arefl (q<r∈upper q p) refl
      case-split (no ¬p) = ¬p


  ¬∈upper-close : (a : ℝ)(p q : ℚ) → ¬ q ∈ a .upper → p < q → ¬ p ∈ a .upper
  ¬∈upper-close a p q ¬q∈upper p<q =
    <upper→¬∈upper a _ (λ r r∈upper → <-trans p<q (¬∈upper→<upper a _ ¬q∈upper r r∈upper))


  {-

    Basic algebraic operations of ℝ

  -}


  -- Additive Inverse

  -upper : (a : ℝ)(x : ℚ) → hProp ℓ-zero
  -upper a x = ∥ Σ[ p ∈ ℚ ] ((r : ℚ) → r ∈ a .upper → p < r) × (x > - p) ∥ , squash

  -ℝ_ : ℝ → ℝ
  (-ℝ a) .upper = specify (-upper a)
  (-ℝ a) .upper-inhab = Prop.map
    (λ (q , q<r∈upper) →
      (- q) + 1 , Inhab→∈ (-upper a) ∣ q , q<r∈upper , q+1>q ∣ )
    (a .lower-inhab)
  (-ℝ a) .upper-close r q q∈upper q<r = Prop.rec (isProp∈ ((-ℝ a) .upper))
    (λ (p , p<r∈upper , q>-p) →
      Inhab→∈ (-upper a) ∣ p , p<r∈upper , <-trans q>-p q<r ∣)
    (∈→Inhab (-upper a) q∈upper)
  (-ℝ a) .upper-round q q∈upper = Prop.map
    (λ (p , p<r∈upper , q>-p) →
      middle (- p) q , middle<r q>-p  , Inhab→∈ (-upper a) ∣ p , p<r∈upper , middle>l q>-p ∣)
    (∈→Inhab (-upper a) q∈upper)
  (-ℝ a) .lower-inhab = Prop.map
    (λ (q , q∈upper) →
      - q , λ r r∈upper → Prop.rec isProp<
        (λ (p , p<s∈upper , r>-p) →
          <-trans (-Reverse< (p<s∈upper q q∈upper)) r>-p)
        (∈→Inhab (-upper a) r∈upper))
    (a .upper-inhab)


  -- Addition

  +upper : ℝ → ℝ → ℚ → hProp ℓ-zero
  +upper a b r = ∥ Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ] p ∈ a .upper × q ∈ b .upper × (r ≡ p + q) ∥ , squash

  private
    alg-helper : (a b c d : ℚ) → d ≡ a + b → c ≡ a + (b + (c - d))
    alg-helper a b c d d≡a+b = helper2 c d ∙ (λ i → c + (d≡a+b i - d)) ∙ helper1 a b c d

  _+ℝ_ : ℝ → ℝ → ℝ
  (a +ℝ b) .upper = specify (+upper a b)
  (a +ℝ b) .upper-inhab = Prop.map2
    (λ (p , p∈upper) (q , q∈upper) →
      p + q , Inhab→∈ (+upper a b) ∣ p , q , p∈upper , q∈upper , refl ∣)
    (a .upper-inhab) (b .upper-inhab)
  (a +ℝ b) .upper-close r q q∈upper q<r = Prop.rec (isProp∈ ((a +ℝ b) .upper))
    (λ (s , t , s∈upper , t∈upper , q≡s+t) →
      let t+r-q∈upper : (t + (r - q)) ∈ b .upper
          t+r-q∈upper = b .upper-close _ _ t∈upper (+-rPos→> (>→Diff>0 q<r))
          r≡s+t+r-q : r ≡ s + (t + (r - q))
          r≡s+t+r-q = alg-helper s t r q q≡s+t
      in  Inhab→∈ (+upper a b) ∣ s , t + (r - q) , s∈upper , t+r-q∈upper , r≡s+t+r-q ∣)
    (∈→Inhab (+upper a b) q∈upper)
  (a +ℝ b) .upper-round q q∈upper = Prop.rec squash
    (λ (s , t , s∈upper , t∈upper , q≡s+t) → Prop.map2
      (λ (s' , s'<s , s'∈upper) (t' , t'<t , t'∈upper) →
        s' + t' , subst (s' + t' <_) (sym q≡s+t) (+-Pres< s'<s t'<t) ,
        Inhab→∈ (+upper a b) ∣ s' , t' , s'∈upper , t'∈upper , refl ∣)
      (a .upper-round s s∈upper) (b .upper-round t t∈upper))
    (∈→Inhab (+upper a b) q∈upper)
  (a +ℝ b) .lower-inhab = Prop.map2
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

  ℝ₊ : Type
  ℝ₊ = Σ[ r ∈ ℝ ] (r ≥ℝ 0)

  path-ℝ₊ : (a b : ℝ₊) → a .fst ≡ b .fst → a ≡ b
  path-ℝ₊ a b p i .fst = p i
  path-ℝ₊ a b p i .snd = isProp→PathP (λ i → isProp≤ℝ {a = 0} {b = p i}) (a .snd) (b .snd) i

  q∈ℝ₊→q>0 : (a : ℝ₊)(q : ℚ) → q ∈ a .fst .upper → q > 0
  q∈ℝ₊→q>0 a q q∈upper = ∈→Inhab (0 <P_) (a .snd q∈upper)


  -- Zero and Unit

  0₊ : ℝ₊
  0₊ = 0 , ≡→⊆ refl

  1₊ : ℝ₊
  1₊ = 1 , λ q∈upper → Inhab→∈ (0 <P_) (<-trans 1>0 (∈→Inhab (1 <P_) q∈upper))


  -- Addition

  +upper₊ : ℝ₊ → ℝ₊ → ℚ → hProp ℓ-zero
  +upper₊ a b = +upper (a .fst) (b .fst)

  _+ℝ₊_ : (a b : ℝ₊) → ℝ₊
  ((a , a≥0) +ℝ₊ (b , b≥0)) .fst = a +ℝ b
  ((a , a≥0) +ℝ₊ (b , b≥0)) .snd q∈upper =
    Prop.rec (isProp∈ (0 .upper))
    (λ (s , t , s∈upper , t∈upper , q≡s+t) →
      let s>0 = ∈→Inhab (0 <P_) (a≥0 s∈upper)
          t>0 = ∈→Inhab (0 <P_) (b≥0 t∈upper)
      in  Inhab→∈ (0 <P_) (subst (_> 0) (sym q≡s+t) (+-Pres>0 s>0 t>0)))
    (∈→Inhab (+upper a b) q∈upper)


  -- Multiplication

  ·upper : ℝ → ℝ → ℚ → hProp ℓ-zero
  ·upper a b r = ∥ Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ] p ∈ a .upper × q ∈ b .upper × (r ≡ p · q) ∥ , squash

  ·upper₊ : ℝ₊ → ℝ₊ → ℚ → hProp ℓ-zero
  ·upper₊ a b = ·upper (a .fst) (b .fst)


  ≥ℝ0+q∈upper→q>0 : (a : ℝ){q : ℚ} → a ≥ℝ 0 → q ∈ a .upper → q > 0
  ≥ℝ0+q∈upper→q>0 a {q = q} a≥0 q∈upper = ∈→Inhab (0 <P_) (a≥0 q∈upper)

  q∈·upper→q>0 : (a b : ℝ) → a ≥ℝ 0 → b ≥ℝ 0 → (q : ℚ) → q ∈ specify (·upper a b) → q > 0
  q∈·upper→q>0 a b a≥0 b≥0 q q∈upper = Prop.rec isProp<
    (λ (s , t , s∈upper , t∈upper , q≡s·t) →
      subst (_> 0) (sym q≡s·t)
        (·-Pres>0 (≥ℝ0+q∈upper→q>0 a a≥0 s∈upper) (≥ℝ0+q∈upper→q>0 b b≥0 t∈upper)))
    (∈→Inhab (·upper a b) q∈upper)

  private
    alg-helper' : (a b c d : ℚ)(d≢0 : ¬ d ≡ 0) → d ≡ a · b → c ≡ a · (b · (c · inv d≢0))
    alg-helper' a b c d d≢0 d≡a·b =
        sym (·Rid c) ∙ (λ i → c · ·-rInv d≢0 (~ i))
      ∙ (λ i → c · (d≡a·b i · inv d≢0)) ∙ helper1' a b c (inv d≢0)

  _·ℝ₊_ : (a b : ℝ₊) → ℝ₊
  ((a , a≥0) ·ℝ₊ (b , b≥0)) .fst .upper = specify (·upper a b)
  ((a , a≥0) ·ℝ₊ (b , b≥0)) .fst .upper-inhab = Prop.map2
    (λ (p , p∈upper) (q , q∈upper) →
      p · q , Inhab→∈ (·upper a b) ∣ p , q , p∈upper , q∈upper , refl ∣)
    (a .upper-inhab) (b .upper-inhab)
  ((a , a≥0) ·ℝ₊ (b , b≥0)) .fst .upper-close r q q∈upper q<r =
    Prop.rec (isProp∈ (((a , a≥0) ·ℝ₊ (b , b≥0)) .fst .upper))
    (λ (s , t , s∈upper , t∈upper , q≡s·t) →
      let q>0 : q > 0
          q>0 = q∈·upper→q>0 a b a≥0 b≥0 q q∈upper
          q≢0 : ¬ q ≡ 0
          q≢0 = >-arefl q>0
          q⁻¹ = inv q≢0
          t·r·q⁻¹∈upper : (t · (r · q⁻¹)) ∈ b .upper
          t·r·q⁻¹∈upper = b .upper-close _ _ t∈upper
            (·-Pos·>1→> (≥ℝ0+q∈upper→q>0 b b≥0 t∈upper) (p>q>0→p·q⁻¹>1 q>0 q<r))
          r≡s·t·r·q⁻¹ : r ≡ s · (t · (r · q⁻¹))
          r≡s·t·r·q⁻¹ = alg-helper' s t r q q≢0 q≡s·t
      in  Inhab→∈ (·upper a b) ∣ s , t · (r · q⁻¹) , s∈upper , t·r·q⁻¹∈upper , r≡s·t·r·q⁻¹ ∣)
    (∈→Inhab (·upper a b) q∈upper)
  ((a , a≥0) ·ℝ₊ (b , b≥0)) .fst .upper-round q q∈upper = Prop.rec squash
    (λ (s , t , s∈upper , t∈upper , q≡s·t) → Prop.map2
      (λ (s' , s'<s , s'∈upper) (t' , t'<t , t'∈upper) →
        s' · t' , subst (s' · t' <_) (sym q≡s·t)
          (·-PosPres> (≥ℝ0+q∈upper→q>0 a a≥0 s'∈upper) (≥ℝ0+q∈upper→q>0 b b≥0 t'∈upper) s'<s t'<t) ,
        Inhab→∈ (·upper a b) ∣ s' , t' , s'∈upper , t'∈upper , refl ∣ )
      (a .upper-round s s∈upper) (b .upper-round t t∈upper))
    (∈→Inhab (·upper a b) q∈upper)
  ((a , a≥0) ·ℝ₊ (b , b≥0)) .fst .lower-inhab =
    ∣ - 1 , (λ r r∈upper → <-trans -1<0 (q∈·upper→q>0 a b a≥0 b≥0 r r∈upper)) ∣
  ((a , a≥0) ·ℝ₊ (b , b≥0)) .snd q∈upper =
    Prop.rec (isProp∈ (0 .upper))
    (λ (s , t , s∈upper , t∈upper , q≡s·t) →
      let s>0 = ∈→Inhab (0 <P_) (a≥0 s∈upper)
          t>0 = ∈→Inhab (0 <P_) (b≥0 t∈upper)
      in  Inhab→∈ (0 <P_) (subst (_> 0) (sym q≡s·t) (·-Pres>0 s>0 t>0)))
    (∈→Inhab (·upper a b) q∈upper)


  -- Multiplicative Inverse

  inv-upper : (a : ℝ)(x : ℚ) → hProp ℓ-zero
  inv-upper a x = ∥ Σ[ p ∈ ℚ ] Σ[ p>0 ∈ p > 0 ] ((r : ℚ) → r ∈ a .upper → p < r) × (x > inv (>-arefl p>0)) ∥ , squash

  invℝ₊ : (a : ℝ)(q : ℚ) → q > 0 → ((r : ℚ) → r ∈ a .upper → q < r) → ℝ₊
  invℝ₊ a _ _ _ .fst .upper = specify (inv-upper a)
  invℝ₊ a q₀ q₀>0 q₀<r∈upper .fst .upper-inhab =
    let q₀⁻¹ = inv (>-arefl q₀>0) in
    ∣ q₀⁻¹ + 1 , Inhab→∈ (inv-upper a) ∣ q₀ , q₀>0 , q₀<r∈upper , q+1>q {q = q₀⁻¹} ∣ ∣
  invℝ₊ a _ _ _ .fst .upper-close r q q∈upper q<r =
    Prop.rec (isProp∈ (invℝ₊ a _ _ _ .fst .upper))
    (λ (p , p>0 , p<r∈upper , q>p⁻¹) →
      Inhab→∈ (inv-upper a) ∣ p , p>0 , p<r∈upper , <-trans q>p⁻¹ q<r ∣)
    (∈→Inhab (inv-upper a) q∈upper)
  invℝ₊ a _ _ _ .fst .upper-round q q∈upper = Prop.map
    (λ (p , p>0 , p<r∈upper , q>p⁻¹) →
      let p⁻¹ = inv (>-arefl p>0) in
      middle p⁻¹ q , middle<r q>p⁻¹  , Inhab→∈ (inv-upper a) ∣ p , p>0 , p<r∈upper , middle>l q>p⁻¹ ∣)
    (∈→Inhab (inv-upper a) q∈upper)
  invℝ₊ a q₀ q₀>0 q₀<r∈upper .fst .lower-inhab = Prop.map
    (λ (q , q∈upper) →
      let q>0 = <-trans q₀>0 (q₀<r∈upper q q∈upper)
          q⁻¹ = inv (>-arefl q>0) in
      q⁻¹ , λ r r∈upper → Prop.rec isProp<
        (λ (p , p>0 , p<s∈upper , r>p⁻¹) →
          <-trans (inv-Reverse< _ _ (p<s∈upper q q∈upper)) r>p⁻¹)
        (∈→Inhab (inv-upper a) r∈upper))
    (a .upper-inhab)
  invℝ₊ a _ _ _ .snd q∈upper =
    Prop.rec (isProp∈ (0 .upper))
    (λ (p , p>0 , p<r∈upper , q>p⁻¹) →
      Inhab→∈ (0 <P_) (<-trans (p>0→p⁻¹>0 p>0) q>p⁻¹))
    (∈→Inhab (inv-upper a) q∈upper)
