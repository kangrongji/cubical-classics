{-

The Real Number

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Analysis.Real.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.Rationals.QuoQ

open import Classical.Preliminary.Rational
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset


module Real (decide : LEM) where

  open Powerset decide

  -- Dedekin Cut

  record DedekindCut : Type where
    field
      lower : ℙ ℚ
      lower-inhab : ∥ Σ[ q ∈ ℚ ] q ∈ lower ∥
      lower-close : (r : ℚ)(q : ℚ) → q ∈ lower → r < q → r ∈ lower
      lower-round : (q : ℚ) → q ∈ lower → ∥ Σ[ r ∈ ℚ ] (q < r) × (r ∈ lower) ∥

      upper : ℙ ℚ
      upper-inhab : ∥ Σ[ q ∈ ℚ ] q ∈ upper ∥
      upper-close : (r : ℚ)(q : ℚ) → q ∈ upper → q < r → r ∈ upper
      upper-round : (q : ℚ) → q ∈ upper → ∥ Σ[ r ∈ ℚ ] (r < q) × (r ∈ upper) ∥

      order : (p q : ℚ) → p ∈ lower → q ∈ upper → p < q

  open DedekindCut


  -- Dedekind Real Number

  ℝ : Type
  ℝ = DedekindCut

  -- Additive Inverse

  -sub : ℙ ℚ → (x : ℚ) → hProp ℓ-zero
  -sub A x = - x ∈ A , isProp∈ A

  -ℝ_ : ℝ → ℝ
  (-ℝ a) .lower = specify (-sub (a .upper))
  (-ℝ a) .lower-inhab = specify (-sub (a .upper))

  -- Addition

  +lower : ℝ → ℝ → ℚ → hProp ℓ-zero
  +lower a b r = ∥ Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ] p ∈ a .lower × q ∈ b .lower × (r ≡ p + q) ∥ , squash

  +upper : ℝ → ℝ → ℚ → hProp ℓ-zero
  +upper a b r = ∥ Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ] p ∈ a .upper × q ∈ b .upper × (r ≡ p + q) ∥ , squash

  private
    alg-helper : (a b c d : ℚ) → d ≡ a + b → c ≡ a + (b + (c - d))
    alg-helper = {!!}

  _+ℝ_ : ℝ → ℝ → ℝ
  (a +ℝ b) .lower = specify (+lower a b)
  (a +ℝ b) .lower-inhab = Prop.map2
    (λ (p , p∈upper) (q , q∈upper) → p + q , Inhab→∈ (+lower a b) ∣ p , q , p∈upper , q∈upper , refl ∣)
    (a .lower-inhab) (b .lower-inhab)
  (a +ℝ b) .lower-close r q q∈lower r<q = Prop.rec (isProp∈ ((a +ℝ b) .lower))
    (λ (s , t , s∈lower , t∈lower , q≡s+t) →
      let t+r-q∈lower : (t + (r - q)) ∈ b .lower
          t+r-q∈lower = b .lower-close _ _ t∈lower (<-+-neg (p<q→p-q<0 r<q))
          r≡s+t+r-q : r ≡ s + (t + (r - q))
          r≡s+t+r-q = alg-helper s t r q q≡s+t
      in  Inhab→∈ (+lower a b) ∣ s , t + (r - q) , s∈lower , t+r-q∈lower , r≡s+t+r-q ∣)
    (∈→Inhab (+lower a b) q∈lower)
  (a +ℝ b) .lower-round q q∈lower = Prop.rec squash
    (λ (s , t , s∈lower , t∈lower , q≡s+t) → Prop.map2
      (λ (s' , s<s' , s'∈lower) (t' , t<t' , t'∈lower) →
        s' + t' , subst (_< s' + t') (sym q≡s+t) (+-<-+ s<s' t<t') ,
        Inhab→∈ (+lower a b) ∣ s' , t' , s'∈lower , t'∈lower , refl ∣ )
      (a .lower-round s s∈lower) (b .lower-round t t∈lower))
    (∈→Inhab (+lower a b) q∈lower)
  (a +ℝ b) .upper = specify (+upper a b)
  (a +ℝ b) .upper-inhab = Prop.map2
    (λ (p , p∈upper) (q , q∈upper) → p + q , Inhab→∈ (+upper a b) ∣ p , q , p∈upper , q∈upper , refl ∣)
    (a .upper-inhab) (b .upper-inhab)
  (a +ℝ b) .upper-close r q q∈upper q<r = Prop.rec (isProp∈ ((a +ℝ b) .upper))
    (λ (s , t , s∈upper , t∈upper , q≡s+t) →
      let t+r-q∈upper : (t + (r - q)) ∈ b .upper
          t+r-q∈upper = b .upper-close _ _ t∈upper (<-+-pos (p>q→p-q>0 q<r))
          r≡s+t+r-q : r ≡ s + (t + (r - q))
          r≡s+t+r-q = alg-helper s t r q q≡s+t
      in  Inhab→∈ (+upper a b) ∣ s , t + (r - q) , s∈upper , t+r-q∈upper , r≡s+t+r-q ∣)
    (∈→Inhab (+upper a b) q∈upper)
  (a +ℝ b) .upper-round q q∈upper = Prop.rec squash
    (λ (s , t , s∈upper , t∈upper , q≡s+t) → Prop.map2
      (λ (s' , s'<s , s'∈upper) (t' , t'<t , t'∈upper) →
        s' + t' , subst (s' + t' <_) (sym q≡s+t) (+-<-+ s'<s t'<t) ,
        Inhab→∈ (+upper a b) ∣ s' , t' , s'∈upper , t'∈upper , refl ∣ )
      (a .upper-round s s∈upper) (b .upper-round t t∈upper))
    (∈→Inhab (+upper a b) q∈upper)
  (a +ℝ b) .order p q p∈lower q∈upper = Prop.rec2 isProp<
    (λ (u , v , u∈lower , v∈lower , p≡u+v) (s , t , s∈upper , t∈upper , q≡s+t) →
      transport (λ i → p≡u+v (~ i) < q≡s+t (~ i))
        (+-<-+ (a .order u s u∈lower s∈upper) (b .order v t v∈lower t∈upper)))
    (∈→Inhab (+lower a b) p∈lower) (∈→Inhab (+upper a b) q∈upper)


  -- ℝ is hSet

  path-ℝ : (a b : DedekindCut) → a .lower ≡ b .lower → a .upper ≡ b .upper → a ≡ b
  path-ℝ a b lower-path upper-path i .lower = lower-path i
  path-ℝ a b lower-path upper-path i .lower-inhab =
    isProp→PathP (λ i → squash {A = Σ[ q ∈ ℚ ] q ∈ lower-path i}) (a .lower-inhab) (b .lower-inhab) i
  path-ℝ a b lower-path upper-path i .lower-round =
    isProp→PathP (λ i → isPropΠ2 {B = λ q → q ∈ lower-path i}
      (λ q _ → squash {A = Σ[ r ∈ ℚ ] (q < r) × (r ∈ lower-path i)}))
    (a .lower-round) (b .lower-round) i
  path-ℝ a b lower-path upper-path i .lower-close =
    isProp→PathP (λ i → isPropΠ4 {C = λ _ q → q ∈ lower-path i} (λ _ _ _ _ → isProp∈ (lower-path i)))
    (a .lower-close) (b .lower-close) i
  path-ℝ a b lower-path upper-path i .upper = upper-path i
  path-ℝ a b lower-path upper-path i .upper-inhab =
    isProp→PathP (λ i → squash {A = Σ[ q ∈ ℚ ] q ∈ upper-path i}) (a .upper-inhab) (b .upper-inhab) i
  path-ℝ a b lower-path upper-path i .upper-close =
    isProp→PathP (λ i → isPropΠ4 {C = λ _ q → q ∈ upper-path i} (λ _ _ _ _ → isProp∈ (upper-path i)))
    (a .upper-close) (b .upper-close) i
  path-ℝ a b lower-path upper-path i .upper-round =
    isProp→PathP (λ i → isPropΠ2 {B = λ q → q ∈ upper-path i}
      (λ q _ → squash {A = Σ[ r ∈ ℚ ] (r < q) × (r ∈ upper-path i)}))
    (a .upper-round) (b .upper-round) i
  path-ℝ a b lower-path upper-path i .order =
    isProp→PathP (λ i → isPropΠ4 {C = λ p _ → p ∈ lower-path i} {D = λ _ q _ → q ∈ upper-path i}
      (λ _ _ _ _ → isProp<)) (a .order) (b .order) i

  isSetℝ : isSet ℝ
  isSetℝ a b p q i j =
    hcomp (λ k → λ
      { (i = i0) → path-ℝ (lift-square i0 j) (p j) refl refl k
      ; (i = i1) → path-ℝ (lift-square i1 j) (q j) refl refl k
      ; (j = i0) → path-ℝ a a refl refl k
      ; (j = i1) → path-ℝ b b refl refl k })
    (lift-square i j)
    where
    lift-square : (i j : I) → ℝ
    lift-square i j = path-ℝ a b
      (isSet→SquareP (λ _ _ → isSetℙ {X = ℚ}) (cong lower p) (cong lower q) refl refl i)
      (isSet→SquareP (λ _ _ → isSetℙ {X = ℚ}) (cong upper p) (cong upper q) refl refl i) j


  -- Rational number is real number

  _<P_ : ℚ → ℚ → hProp ℓ-zero
  _<P_ p q = (p < q) , isProp<

  ℚ→ℝ : ℚ → ℝ
  ℚ→ℝ q .lower = specify (_<P q)
  ℚ→ℝ q .lower-inhab = ∣ q - 1 , Inhab→∈ (_<P q) q-1<q ∣
  ℚ→ℝ q .lower-close r s s∈lower r<s = Inhab→∈ (_<P q) (<-trans r<s (∈→Inhab (_<P q) s∈lower))
  ℚ→ℝ q .lower-round r r∈lower = ∣ middle r q , middle>l r<q , Inhab→∈ (_<P q) (middle<r r<q) ∣
    where r<q : r < q
          r<q = ∈→Inhab (_<P q) r∈lower
  ℚ→ℝ q .upper = specify (q <P_)
  ℚ→ℝ q .upper-inhab = ∣ q + 1 , Inhab→∈ (q <P_) q+1>q ∣
  ℚ→ℝ q .upper-close r s s∈upper r>s = Inhab→∈ (q <P_) (<-trans (∈→Inhab (q <P_) s∈upper) r>s)
  ℚ→ℝ q .upper-round r r∈upper = ∣ middle q r , middle<r r>q , Inhab→∈ (q <P_) (middle>l r>q) ∣
    where r>q : r > q
          r>q = ∈→Inhab (q <P_) r∈upper
  ℚ→ℝ q .order r s r∈lower s∈upper = <-trans (∈→Inhab (_<P q) r∈lower) (∈→Inhab (q <P_) s∈upper)


  -- A criterion for being zero

  --r∉lower+r∉upper→r≡0 : (r : ℝ) → 0 ∉ r .lower → 0 ∉ r .upper → r ≡ 0
  --r∉lower+r∉upper→r≡0 = {!!}

  -- The natural order on ℝ

  _≤ℝ_ : ℝ → ℝ → Type
  a ≤ℝ b = (a .lower ⊆ b .lower) × (b .upper ⊆ a .upper)

  ≤-lower : (a b : ℝ) → a .lower ⊆ b .lower → a ≤ℝ b
  ≤-lower a b a⊆b = {!!}

  ≤-upper : (a b : ℝ) → b .upper ⊆ a .upper → a ≤ℝ b
  ≤-upper a b a⊆b = {!!}

  -- Positive and negative integer literals for ℝ

  instance
    fromNatℝ : HasFromNat ℝ
    fromNatℝ = record { Constraint = λ _ → Unit ; fromNat = λ n → ℚ→ℝ (  ℕ→ℚ n) }

  instance
    fromNegℝ : HasFromNeg ℝ
    fromNegℝ = record { Constraint = λ _ → Unit ; fromNeg = λ n → ℚ→ℝ (- ℕ→ℚ n) }
