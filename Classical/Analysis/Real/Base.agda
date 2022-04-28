{-

The Real Number

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Analysis.Real.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.Rationals.QuoQ

open import Classical.Preliminary.PropositionalTruncation as Prop
open import Classical.Preliminary.Rational
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset


module Real (decide : LEM) where

  open Powerset decide

  {-

    Dedekind Cut

  -}

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


  {-

    hLevel of ℝ

  -}

  -- Construct path in ℝ from path of two cuts

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

  -- ℝ is hSet

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


  {-

    Algebraic Operations of ℝ

  -}


  -- Additive Inverse

  -sub : ℙ ℚ → (x : ℚ) → hProp ℓ-zero
  -sub A x = - x ∈ A , isProp∈ A

  ∈-sub : {q : ℚ}(A : ℙ ℚ) → q ∈ A → - q ∈ specify (-sub A)
  ∈-sub {q = q} A q∈A = Inhab→∈ (-sub A) {x = - q} (subst (_∈ A) (sym -Involutive) q∈A)

  -ℝ_ : ℝ → ℝ
  (-ℝ a) .lower = specify (-sub (a .upper))
  (-ℝ a) .lower-inhab = Prop.map
    (λ (p , p∈upper) → - p , ∈-sub (a .upper) p∈upper) (a .upper-inhab)
  (-ℝ a) .lower-close r q q∈lower r<q =
    Inhab→∈ (-sub (a .upper)) {x = r} (a .upper-close _ _ -q∈upper (-reverse< r<q))
    where -q∈upper : - q ∈ a .upper
          -q∈upper = ∈→Inhab (-sub (a .upper)) {x = q} q∈lower
  (-ℝ a) .lower-round q q∈lower = Prop.map
    (λ (r , r<-q , r∈upper) →
        - r , subst (_< - r) -Involutive (-reverse< r<-q) , ∈-sub (a .upper) r∈upper)
    (a .upper-round _ -q∈upper)
    where -q∈upper : - q ∈ a .upper
          -q∈upper = ∈→Inhab (-sub (a .upper)) {x = q} q∈lower
  (-ℝ a) .upper = specify (-sub (a .lower))
  (-ℝ a) .upper-inhab = Prop.map
    (λ (p , p∈lower) → - p , ∈-sub (a .lower) p∈lower) (a .lower-inhab)
  (-ℝ a) .upper-close r q q∈upper q<r =
    Inhab→∈ (-sub (a .lower)) {x = r} (a .lower-close _ _ -q∈lower (-reverse< q<r))
    where -q∈lower : - q ∈ a .lower
          -q∈lower = ∈→Inhab (-sub (a .lower)) {x = q} q∈upper
  (-ℝ a) .upper-round q q∈upper = Prop.map
    (λ (r , -q<r , r∈lower) →
        - r , subst (- r <_) -Involutive (-reverse< -q<r) , ∈-sub (a .lower) r∈lower)
    (a .lower-round _ -q∈lower)
    where -q∈lower : - q ∈ a .lower
          -q∈lower = ∈→Inhab (-sub (a .lower)) {x = q} q∈upper
  (-ℝ a) .order p q p∈lower q∈upper = -reverse<' (a .order _ _ -q∈lower -p∈upper)
    where -p∈upper : - p ∈ a .upper
          -p∈upper = ∈→Inhab (-sub (a .upper)) {x = p} p∈lower
          -q∈lower : - q ∈ a .lower
          -q∈lower = ∈→Inhab (-sub (a .lower)) {x = q} q∈upper


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


  -- Multiplication

  open Min4
  open Max4
  open Middle4

  ·lower : ℝ → ℝ → ℚ → hProp ℓ-zero
  ·lower a b r =
    ∥ Σ[ x ∈ ℚ ] Σ[ y ∈ ℚ ] Σ[ z ∈ ℚ ] Σ[ w ∈ ℚ ]
      x ∈ a .lower × y ∈ a .upper × z ∈ b .lower × w ∈ b .upper
    × (r < min4 (x · z) (x · w) (y · z) (y · w) .num) ∥ , squash

  ·upper : ℝ → ℝ → ℚ → hProp ℓ-zero
  ·upper a b r =
    ∥ Σ[ x ∈ ℚ ] Σ[ y ∈ ℚ ] Σ[ z ∈ ℚ ] Σ[ w ∈ ℚ ]
      x ∈ a .lower × y ∈ a .upper × z ∈ b .lower × w ∈ b .upper
    × (r > max4 (x · z) (x · w) (y · z) (y · w) .num) ∥ , squash

  _·ℝ_ : ℝ → ℝ → ℝ
  (a ·ℝ b) .lower = specify (·lower a b)
  (a ·ℝ b) .lower-inhab = Prop.map4
    (λ (x , x∈lower) (y , y∈upper) (z , z∈lower) (w , w∈upper) →
       min4 (x · z) (x · w) (y · z) (y · w) .num - 1 ,
       Inhab→∈ (·lower a b) ∣ x , y , z , w , x∈lower , y∈upper , z∈lower , w∈upper , q-1<q ∣)
    (a .lower-inhab) (a .upper-inhab) (b .lower-inhab) (b .upper-inhab)
  (a ·ℝ b) .lower-close r q q∈lower r<q = Prop.rec (isProp∈ ((a ·ℝ b) .lower))
    (λ (x , y , z , w , x∈lower , y∈upper , z∈lower , w∈upper , q<min) →
      Inhab→∈ (·lower a b) ∣ x , y , z , w , x∈lower , y∈upper , z∈lower , w∈upper , <-trans r<q q<min ∣)
    (∈→Inhab (·lower a b) q∈lower)
  (a ·ℝ b) .lower-round q q∈lower = Prop.map
    (λ (x , y , z , w , x∈lower , y∈upper , z∈lower , w∈upper , q<min) →
      let min = min4 (x · z) (x · w) (y · z) (y · w) .num in
      middle q min , middle>l q<min ,
      Inhab→∈ (·lower a b) ∣ x , y , z , w , x∈lower , y∈upper , z∈lower , w∈upper , middle<r q<min ∣)
    (∈→Inhab (·lower a b) q∈lower)
  (a ·ℝ b) .upper = specify (·upper a b)
  (a ·ℝ b) .upper-inhab = Prop.map4
    (λ (x , x∈lower) (y , y∈upper) (z , z∈lower) (w , w∈upper) →
       max4 (x · z) (x · w) (y · z) (y · w) .num + 1 ,
       Inhab→∈ (·upper a b) ∣ x , y , z , w , x∈lower , y∈upper , z∈lower , w∈upper , q+1>q ∣)
    (a .lower-inhab) (a .upper-inhab) (b .lower-inhab) (b .upper-inhab)
  (a ·ℝ b) .upper-close r q q∈upper r>q = Prop.rec (isProp∈ ((a ·ℝ b) .upper))
    (λ (x , y , z , w , x∈lower , y∈upper , z∈lower , w∈upper , q>max) →
      Inhab→∈ (·upper a b) ∣ x , y , z , w , x∈lower , y∈upper , z∈lower , w∈upper , <-trans q>max r>q ∣)
    (∈→Inhab (·upper a b) q∈upper)
  (a ·ℝ b) .upper-round q q∈upper = Prop.map
    (λ (x , y , z , w , x∈lower , y∈upper , z∈lower , w∈upper , q>max) →
      let max = max4 (x · z) (x · w) (y · z) (y · w) .num in
      middle max q , middle<r q>max ,
      Inhab→∈ (·upper a b) ∣ x , y , z , w , x∈lower , y∈upper , z∈lower , w∈upper , middle>l q>max ∣)
    (∈→Inhab (·upper a b) q∈upper)
  (a ·ℝ b) .order p q p∈lower q∈upper = Prop.rec2 isProp<
    (λ (x₁ , y₁ , z₁ , w₁ , x₁∈lower , y₁∈upper , z₁∈lower , w₁∈upper , p<min₁)
       (x₂ , y₂ , z₂ , w₂ , x₂∈lower , y₂∈upper , z₂∈lower , w₂∈upper , q>max₂) →
      let mid₁ = middle4
            (a .order x₁ y₁ x₁∈lower y₁∈upper) (a .order x₁ y₂ x₁∈lower y₂∈upper)
            (a .order x₂ y₁ x₂∈lower y₁∈upper) (a .order x₂ y₂ x₂∈lower y₂∈upper)
          mid₂ = middle4
            (b .order z₁ w₁ z₁∈lower w₁∈upper) (b .order z₁ w₂ z₁∈lower w₂∈upper)
            (b .order z₂ w₁ z₂∈lower w₁∈upper) (b .order z₂ w₂ z₂∈lower w₂∈upper)
          min₁<mid₁·mid₂ = ·interval-min (mid₁ .>₁) (mid₁ .<₁) (mid₂ .>₁) (mid₂ .<₁)
          mid₁·mid₂<max₂ = ·interval-max (mid₁ .>₂) (mid₁ .<₂) (mid₂ .>₂) (mid₂ .<₂)
      in  <-trans (<-trans p<min₁ (<-trans min₁<mid₁·mid₂ mid₁·mid₂<max₂)) q>max₂)
    (∈→Inhab (·lower a b) p∈lower) (∈→Inhab (·upper a b) q∈upper)


  {-

    Inclusion of ℚ into ℝ

  -}

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

  ≡q→q∉lower : (r : ℝ)(q : ℚ) → r ≡ ℚ→ℝ q → q ∉ r .lower
  ≡q→q∉lower = {!!}

  ≡q→q∉upper : (r : ℝ)(q : ℚ) → r ≡ ℚ→ℝ q → q ∉ r .upper
  ≡q→q∉upper = {!!}

  q∉lower+q∉upper→≡q : (r : ℝ)(q : ℚ) → q ∉ r .lower → q ∉ r .upper → r ≡ ℚ→ℝ q
  q∉lower+q∉upper→≡q = {!!}

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
