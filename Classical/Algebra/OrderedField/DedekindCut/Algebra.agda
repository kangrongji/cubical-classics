{-

Algebraic Operations on Dedekind Cuts

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.DedekindCut.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection

open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.DedekindCut.Base
open import Classical.Algebra.OrderedField.DedekindCut.Archimedes

private
  variable
    ℓ ℓ' : Level

private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (q r : 𝓡 .fst) → q ≡ r + (q - r)
    helper1 = solve 𝓡

    helper2 : (q r : 𝓡 .fst) → q ≡ (q + r) - r
    helper2 = solve 𝓡

    helper3 : (p q r : 𝓡 .fst) → q · (p · r) ≡ p · (q · r)
    helper3 = solve 𝓡

    helper4 : (q r : 𝓡 .fst) → r + (r · (q - 1r)) ≡ r · q
    helper4 = solve 𝓡


module Algebra (decide : LEM)
  (𝒦 : OrderedField ℓ ℓ')(archimedesK : isArchimedean (𝒦 . fst))
  where

  private
    K = 𝒦 .fst .fst .fst

  open Powerset decide

  open OrderedFieldStr 𝒦
  open Basics     decide 𝒦
  open Archimedes decide 𝒦 archimedesK
  open DedekindCut

  open Helpers (𝒦 .fst .fst)


  {-

    Addition

  -}

  +𝕂-Comm : (a b : 𝕂) → a +𝕂 b ≡ b +𝕂 a
  +𝕂-Comm a b = ≤𝕂-asym (upper⊆ b a) (upper⊆ a b)
    where
    upper⊆ : (a b : 𝕂){q : K} → q ∈ (a +𝕂 b) .upper → q ∈ (b +𝕂 a) .upper
    upper⊆ a b {q = q} q∈upper = Inhab→∈ (+upper b a) (Prop.map
      (λ (s , t , s∈upper , t∈upper , q≡s+t) → t , s , t∈upper , s∈upper , q≡s+t ∙ +Comm s t)
      (∈→Inhab (+upper a b) q∈upper))


  +𝕂-Assoc : (a b c : 𝕂) → a +𝕂 (b +𝕂 c) ≡ (a +𝕂 b) +𝕂 c
  +𝕂-Assoc a b c = ≤𝕂-asym upper⊇ upper⊆
    where
    upper⊆ : {q : K} → q ∈ (a +𝕂 (b +𝕂 c)) .upper → q ∈ ((a +𝕂 b) +𝕂 c) .upper
    upper⊆ {q = q} q∈upper = Inhab→∈ (+upper (a +𝕂 b) c)
      (Prop.rec squash
      (λ (s , t , s∈upper , t∈upper , q≡s+t) →
        Prop.map
        (λ (r , w , r∈upper , w∈upper , t≡r+w) →
          s + r , w ,
          Inhab→∈ (+upper a b) ∣ s , r , s∈upper , r∈upper , refl ∣ ,
          w∈upper , q≡s+t ∙ (λ i → s + t≡r+w i) ∙ +Assoc s r w)
        (∈→Inhab (+upper b c) t∈upper))
      (∈→Inhab (+upper a (b +𝕂 c)) q∈upper))

    upper⊇ : {q : K} → q ∈ ((a +𝕂 b) +𝕂 c) .upper → q ∈ (a +𝕂 (b +𝕂 c)) .upper
    upper⊇ {q = q} q∈upper = Inhab→∈ (+upper a (b +𝕂 c))
      (Prop.rec squash
      (λ (s , t , s∈upper , t∈upper , q≡s+t) →
        Prop.map
        (λ (r , w , r∈upper , w∈upper , s≡r+w) →
          r , w + t ,
          r∈upper , Inhab→∈ (+upper b c) ∣ w , t , w∈upper , t∈upper , refl ∣ ,
          q≡s+t ∙ (λ i → s≡r+w i + t) ∙ sym (+Assoc r w t))
        (∈→Inhab (+upper a b) s∈upper))
      (∈→Inhab (+upper (a +𝕂 b) c) q∈upper))


  +𝕂-rUnit : (a : 𝕂) → a +𝕂 𝟘 ≡ a
  +𝕂-rUnit a = ≤𝕂-asym upper⊇ upper⊆
    where
    upper⊆ : {q : K} → q ∈ (a +𝕂 𝟘) .upper → q ∈ a .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ (a .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s+t) →
        subst (_∈ a .upper) (sym q≡s+t)
          (a .upper-close (s + t) s s∈upper (+-rPos→> (∈→Inhab (0r <P_) t∈upper))))
      (∈→Inhab (+upper a 𝟘) q∈upper)

    upper⊇ : {q : K} → q ∈ a .upper → q ∈ (a +𝕂 𝟘) .upper
    upper⊇ {q = q} q∈upper = Prop.rec (isProp∈ ((a +𝕂 𝟘) .upper))
      (λ (r , r<q , r∈upper) →
        Inhab→∈ (+upper a 𝟘) ∣ r , q - r , r∈upper ,
        Inhab→∈ (0r <P_) (>→Diff>0 r<q) , helper1 q r ∣)
      (a .upper-round q q∈upper)


  +𝕂-rInverse : (a : 𝕂) → a +𝕂 (-𝕂 a) ≡ 𝟘
  +𝕂-rInverse a = ≤𝕂-asym upper⊇ upper⊆
    where
    upper⊆ : {q : K} → q ∈ (a +𝕂 (-𝕂 a)) .upper → q ∈ 𝟘 .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ (𝟘 .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s+t) → Prop.rec (isProp∈ (𝟘 .upper))
        (λ (p , p<r∈upper , t>-p) →
          let p<s : p < s
              p<s = p<r∈upper s s∈upper
              -p>-s : - p > - s
              -p>-s = -Reverse< p<s
              s+t>s-s : s + t > s - s
              s+t>s-s = <-trans (+-lPres< {z = s} -p>-s) (+-lPres< {z = s} t>-p)
              s+t>0 : s + t > 0r
              s+t>0 = subst (s + t >_) (+Rinv s) s+t>s-s
              q>0 : q > 0r
              q>0 = subst (_> 0r) (sym q≡s+t) s+t>0
          in  Inhab→∈ (0r <P_) q>0)
        (∈→Inhab (-upper a) t∈upper))
      (∈→Inhab (+upper a (-𝕂 a)) q∈upper)

    upper⊇ : {q : K} → q ∈ 𝟘 .upper → q ∈ (a +𝕂 (-𝕂 a)) .upper
    upper⊇ {q = q} q∈upper =
      let q>0 = ∈→Inhab (0r <P_) q∈upper in
      Prop.rec (isProp∈ ((a +𝕂 (-𝕂 a)) .upper))
      (λ (r , s , s<q∈upper , r<s , r+q∈upper) →
        Inhab→∈ (+upper a (-𝕂 a)) ∣ q + r , - r ,
        subst (_∈ a .upper) (+Comm r q) r+q∈upper ,
        Inhab→∈ (-upper a) ∣ s , s<q∈upper , -Reverse< r<s ∣ ,
        helper2 q r ∣)
      (archimedes a q q>0)


  +𝕂-lUnit : (a : 𝕂) → 𝟘 +𝕂 a ≡ a
  +𝕂-lUnit a = +𝕂-Comm 𝟘 a ∙ +𝕂-rUnit a

  +𝕂-lInverse : (a : 𝕂) → (-𝕂 a) +𝕂 a ≡ 𝟘
  +𝕂-lInverse a = +𝕂-Comm (-𝕂 a) a ∙ +𝕂-rInverse a

  -𝕂-Involutive : (a : 𝕂) → -𝕂 (-𝕂 a) ≡ a
  -𝕂-Involutive a =
      sym (+𝕂-rUnit (-𝕂 (-𝕂 a)))
    ∙ (λ i → (-𝕂 (-𝕂 a)) +𝕂 (+𝕂-lInverse a (~ i)))
    ∙ +𝕂-Assoc (-𝕂 (-𝕂 a)) (-𝕂 a) a
    ∙ (λ i → (+𝕂-lInverse (-𝕂 a) i) +𝕂 a)
    ∙ +𝕂-lUnit a

  {-

    Multiplication of Non-Negative Reals

  -}

  ·𝕂₊-Comm : (a b : 𝕂₊) → a ·𝕂₊ b ≡ b ·𝕂₊ a
  ·𝕂₊-Comm a b = path-𝕂₊ _ _ (≤𝕂-asym (upper⊆ b a) (upper⊆ a b))
    where
    upper⊆ : (a b : 𝕂₊){q : K} → q ∈ (a ·𝕂₊ b) .fst .upper → q ∈ (b ·𝕂₊ a) .fst .upper
    upper⊆ (a , a≥0) (b , b≥0) {q = q} q∈upper = Inhab→∈ (·upper b a) (Prop.map
      (λ (s , t , s∈upper , t∈upper , q≡s·t) → t , s , t∈upper , s∈upper , q≡s·t ∙ ·Comm s t)
      (∈→Inhab (·upper a b) q∈upper))


  ·𝕂₊-Assoc : (a b c : 𝕂₊) → a ·𝕂₊ (b ·𝕂₊ c) ≡ (a ·𝕂₊ b) ·𝕂₊ c
  ·𝕂₊-Assoc a b c = path-𝕂₊ _ _ (≤𝕂-asym upper⊇ upper⊆)
    where
    upper⊆ : {q : K} → q ∈ (a ·𝕂₊ (b ·𝕂₊ c)) .fst .upper → q ∈ ((a ·𝕂₊ b) ·𝕂₊ c) .fst .upper
    upper⊆ {q = q} q∈upper = Inhab→∈ (·upper₊ (a ·𝕂₊ b) c)
      (Prop.rec squash
      (λ (s , t , s∈upper , t∈upper , q≡s·t) →
        Prop.map
        (λ (r , w , r∈upper , w∈upper , t≡r·w) →
          s · r , w ,
          Inhab→∈ (·upper₊ a b) ∣ s , r , s∈upper , r∈upper , refl ∣ ,
          w∈upper , q≡s·t ∙ (λ i → s · t≡r·w i) ∙ ·Assoc s r w)
        (∈→Inhab (·upper₊ b c) t∈upper))
      (∈→Inhab (·upper₊ a (b ·𝕂₊ c)) q∈upper))

    upper⊇ : {q : K} → q ∈ ((a ·𝕂₊ b) ·𝕂₊ c) .fst .upper → q ∈ (a ·𝕂₊ (b ·𝕂₊ c)) .fst .upper
    upper⊇ {q = q} q∈upper = Inhab→∈ (·upper₊ a (b ·𝕂₊ c))
      (Prop.rec squash
      (λ (s , t , s∈upper , t∈upper , q≡s·t) →
        Prop.map
        (λ (r , w , r∈upper , w∈upper , s≡r·w) →
          r , w · t ,
          r∈upper , Inhab→∈ (·upper₊ b c) ∣ w , t , w∈upper , t∈upper , refl ∣ ,
          q≡s·t ∙ (λ i → s≡r·w i · t) ∙ sym (·Assoc r w t))
        (∈→Inhab (·upper₊ a b) s∈upper))
      (∈→Inhab (·upper₊ (a ·𝕂₊ b) c) q∈upper))


  private
    alg-helper : (p q : K)(p≢0 : ¬ p ≡ 0r) → q ≡ p · (q · inv p≢0)
    alg-helper p q p≢0 = sym (·Rid q) ∙ (λ i → q · ·-rInv p≢0 (~ i)) ∙ helper3 p q (inv p≢0)


  ·𝕂₊-rZero : (a : 𝕂₊) → a ·𝕂₊ 𝟘₊ ≡ 𝟘₊
  ·𝕂₊-rZero a = path-𝕂₊ _ _ (≤𝕂-asym upper⊇ upper⊆)
    where
    upper⊆ : {q : K} → q ∈ (a ·𝕂₊ 𝟘₊) .fst .upper → q ∈ 𝟘 .upper
    upper⊆ = (a ·𝕂₊ 𝟘₊) .snd

    upper⊇ : {q : K} → q ∈ 𝟘 .upper → q ∈ (a ·𝕂₊ 𝟘₊) .fst .upper
    upper⊇ {q = q} q∈upper = Prop.rec (isProp∈ ((a ·𝕂₊ 𝟘₊) .fst .upper))
      (λ (p , p∈upper) →
        let q>0 = ∈→Inhab (0r <P_) q∈upper
            p>0 = q∈𝕂₊→q>0 a p p∈upper
            p≢0 = >-arefl p>0
            p⁻¹ = inv p≢0 in
        Inhab→∈ (·upper₊ a 𝟘₊) ∣ p , q · p⁻¹ , p∈upper ,
        Inhab→∈ (0r <P_) (·-Pres>0 q>0 (p>0→p⁻¹>0 p>0)) , alg-helper p q p≢0 ∣)
      (a .fst .upper-inhab)


  ·𝕂₊-rUnit : (a : 𝕂₊) → a ·𝕂₊ 𝟙₊ ≡ a
  ·𝕂₊-rUnit a = path-𝕂₊ _ _ (≤𝕂-asym upper⊇ upper⊆)
    where
    upper⊆ : {q : K} → q ∈ (a ·𝕂₊ 𝟙₊) .fst .upper → q ∈ a .fst .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ (a .fst .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s·t) →
        let s>0 = q∈𝕂₊→q>0 a s s∈upper in
        subst (_∈ a .fst .upper) (sym q≡s·t)
          (a .fst .upper-close (s · t) s s∈upper (·-Pos·>1→> s>0 (∈→Inhab (1r <P_) t∈upper))))
      (∈→Inhab (·upper₊ a 𝟙₊) q∈upper)

    upper⊇ : {q : K} → q ∈ a .fst .upper → q ∈ (a ·𝕂₊ 𝟙₊) .fst .upper
    upper⊇ {q = q} q∈upper = Prop.rec (isProp∈ ((a ·𝕂₊ 𝟙₊) .fst .upper))
      (λ (r , r<q , r∈upper) →
        let r>0 = q∈𝕂₊→q>0 a r r∈upper
            r≢0 = >-arefl r>0
            r⁻¹ = inv r≢0 in
        Inhab→∈ (·upper₊ a 𝟙₊) ∣ r , q · r⁻¹ , r∈upper ,
        Inhab→∈ (1r <P_) (p>q>0→p·q⁻¹>1  r>0 r<q) , alg-helper r q r≢0 ∣)
      (a .fst .upper-round q q∈upper)


  private
    upper-round2 : (a : 𝕂)(p q : K) → p ∈ a .upper → q ∈ a .upper → ∥ Σ[ r ∈ K ] (r < p) × (r < q) × (r ∈ a .upper) ∥
    upper-round2 a p q p∈upper q∈upper = Prop.map2
      (λ (r , r<p , r∈upper) (s , s<q , s∈upper) →
        case trichotomy r s of λ
        { (lt r<s) → r , r<p , <-trans r<s s<q , r∈upper
        ; (eq r≡s) → s , subst (_< p) r≡s r<p , s<q , s∈upper
        ; (gt r>s) → s , <-trans r>s r<p , s<q , s∈upper })
      (a .upper-round p p∈upper)
      (a .upper-round q q∈upper)

  ·𝕂₊-lDistrib : (a b c : 𝕂₊) → (a ·𝕂₊ b) +𝕂₊ (a ·𝕂₊ c) ≡ a ·𝕂₊ (b +𝕂₊ c)
  ·𝕂₊-lDistrib a b c = path-𝕂₊ _ _ (≤𝕂-asym upper⊇ upper⊆)
    where
    upper⊆ : {q : K} → q ∈ ((a ·𝕂₊ b) +𝕂₊ (a ·𝕂₊ c)) .fst .upper → q ∈ (a ·𝕂₊ (b +𝕂₊ c)) .fst .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ ((a ·𝕂₊ (b +𝕂₊ c)) .fst .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s+t) →
        Prop.rec2 (isProp∈ ((a ·𝕂₊ (b +𝕂₊ c)) .fst .upper))
        (λ (r , w , r∈upper , w∈upper , s≡r·w)
           (u , v , u∈upper , v∈upper , t≡u·v) →
          Prop.rec (isProp∈ ((a ·𝕂₊ (b +𝕂₊ c)) .fst .upper))
          (λ (x , x<r , x<u , x∈upper) →
            let x>0 = q∈𝕂₊→q>0 a x x∈upper
                w>0 = q∈𝕂₊→q>0 b w w∈upper
                v>0 = q∈𝕂₊→q>0 c v v∈upper
                x·w+x·v<r·w+u·v : (x · w) + (x · v) < (r · w) + (u · v)
                x·w+x·v<r·w+u·v = +-Pres< (·-rPosPres< w>0 x<r) (·-rPosPres< v>0 x<u)
                x·[w+v]<r·w+u·v : x · (w + v) < (r · w) + (u · v)
                x·[w+v]<r·w+u·v = subst (_< ((r · w) + (u · v))) (sym (·Rdist+ x w v)) x·w+x·v<r·w+u·v
                x·[w+v]∈upper : x · (w + v) ∈ (a ·𝕂₊ (b +𝕂₊ c)) .fst .upper
                x·[w+v]∈upper = Inhab→∈ (·upper₊ a (b +𝕂₊ c))
                  ∣ x , w + v , x∈upper ,
                    Inhab→∈ (+upper₊ b c) ∣ w , v , w∈upper , v∈upper , refl ∣ , refl ∣
                r·w+u·v≡q : (r · w) + (u · v) ≡ q
                r·w+u·v≡q = (λ i → s≡r·w (~ i) + t≡u·v (~ i)) ∙ sym q≡s+t
                x·[w+v]<q : x · (w + v) < q
                x·[w+v]<q = subst (x · (w + v) <_) r·w+u·v≡q x·[w+v]<r·w+u·v
            in  (a ·𝕂₊ (b +𝕂₊ c)) .fst .upper-close _ _ x·[w+v]∈upper x·[w+v]<q)
            (upper-round2 (a .fst) r u r∈upper u∈upper))
        (∈→Inhab (·upper₊ a b) s∈upper)
        (∈→Inhab (·upper₊ a c) t∈upper))
      (∈→Inhab (+upper₊ (a ·𝕂₊ b) (a ·𝕂₊ c)) q∈upper)

    upper⊇ : {q : K} → q ∈ (a ·𝕂₊ (b +𝕂₊ c)) .fst .upper → q ∈ ((a ·𝕂₊ b) +𝕂₊ (a ·𝕂₊ c)) .fst .upper
    upper⊇ {q = q} q∈upper = Inhab→∈ (+upper₊ (a ·𝕂₊ b) (a ·𝕂₊ c))
      (Prop.rec squash
      (λ (s , t , s∈upper , t∈upper , q≡s·t) →
        Prop.map
        (λ (r , w , r∈upper , w∈upper , t≡r+w) →
          s · r , s · w ,
          Inhab→∈ (·upper₊ a b) ∣ s , r , s∈upper , r∈upper , refl ∣ ,
          Inhab→∈ (·upper₊ a c) ∣ s , w , s∈upper , w∈upper , refl ∣ ,
          q≡s·t ∙ cong (s ·_) t≡r+w ∙ ·Rdist+ s r w)
        (∈→Inhab (+upper₊ b c) t∈upper))
      (∈→Inhab (·upper₊ a (b +𝕂₊ c)) q∈upper))


  -- Multiplicative Inverse

  module _
    (a₊@(a , a≥0) : 𝕂₊)(q₀ : K)(q₀>0 : q₀ > 0r)
    (q₀<r∈upper : ((r : K) → r ∈ a .upper → q₀ < r)) where

    private
      a⁻¹ : 𝕂₊
      a⁻¹ = inv𝕂₊ a q₀ q₀>0 q₀<r∈upper

      a·a⁻¹ = (a₊ ·𝕂₊ a⁻¹) .fst

      ineq-helper : (r q q' : K) → q - 1r > 0r → r > q' → r + (q' · (q - 1r)) < r · q
      ineq-helper r q q' q-1>0 r>q' = subst (r + (q' · (q - 1r)) <_) (helper4 q r) r+·<r+·
        where r+·<r+· : r + (q' · (q - 1r)) < r + (r · (q - 1r))
              r+·<r+· = +-lPres< (·-rPosPres< q-1>0 r>q')

    ·𝕂₊-rInv : a·a⁻¹ ≡ 𝟙
    ·𝕂₊-rInv = ≤𝕂-asym upper⊇ upper⊆
      where
      upper⊆ : {q : K} → q ∈ a·a⁻¹ .upper → q ∈ 𝟙 .upper
      upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ (𝟙 .upper))
        (λ (s , t , s∈upper , t∈upper , q≡s·t) → Prop.rec (isProp∈ (𝟙 .upper))
          (λ (p , p>0 , p<r∈upper , t>p⁻¹) →
            let p<s : p < s
                p<s = p<r∈upper s s∈upper
                s>0 : s > 0r
                s>0 = <-trans q₀>0 (q₀<r∈upper s s∈upper)
                p⁻¹ = inv (>-arefl p>0)
                s⁻¹ = inv (>-arefl s>0)
                p⁻¹>s⁻¹ : p⁻¹ > s⁻¹
                p⁻¹>s⁻¹ = inv-Reverse< s>0 p>0 p<s
                s·t>s·s⁻¹ : s · t > s · s⁻¹
                s·t>s·s⁻¹ = <-trans (·-lPosPres< {x = s} s>0 p⁻¹>s⁻¹) (·-lPosPres< {x = s} s>0 t>p⁻¹)
                s·t>1 : s · t > 1r
                s·t>1 = subst (s · t >_) (·-rInv (>-arefl s>0)) s·t>s·s⁻¹
                q>1 : q > 1r
                q>1 = subst (_> 1r) (sym q≡s·t) s·t>1
            in  Inhab→∈ (1r <P_) q>1)
          (∈→Inhab (inv-upper a) t∈upper))
        (∈→Inhab (·upper₊ a₊ a⁻¹) q∈upper)

      upper⊇ : {q : K} → q ∈ 𝟙 .upper → q ∈ a·a⁻¹ .upper
      upper⊇ {q = q} q∈upper =
        let q>1 = ∈→Inhab (1r <P_) q∈upper
            q-1>0 : q - 1r > 0r
            q-1>0 = subst (q - 1r >_) (+Rinv 1r) (+-rPres< {z = - 1r} q>1)
            q' = middle 0r q₀
            q'>0 : q' > 0r
            q'>0 = middle>l q₀>0
            q'<q₀ : q' < q₀
            q'<q₀ = middle<r q₀>0
            ε = q' · (q - 1r)
            ε>0 : ε > 0r
            ε>0 = ·-Pres>0 q'>0 q-1>0 in
        Prop.rec (isProp∈ (a·a⁻¹ .upper))
          (λ (r , s , s<q∈upper , q'<r , r<s , r+ε∈upper) →
            let r+ε<r·q : r + ε < r · q
                r+ε<r·q = ineq-helper r q q' q-1>0 q'<r
                r·q∈upper : r · q ∈ a .upper
                r·q∈upper = a .upper-close _ _ r+ε∈upper r+ε<r·q
                r>0 : r > 0r
                r>0 = <-trans q'>0 q'<r
                r⁻¹ = inv (>-arefl r>0)
                s>0 : s > 0r
                s>0 = <-trans r>0 r<s
                r⁻¹∈upper : r⁻¹ ∈ a⁻¹ .fst .upper
                r⁻¹∈upper = Inhab→∈ (inv-upper a)
                  ∣ s , s>0 , s<q∈upper , inv-Reverse< s>0 r>0 r<s ∣
            in  Inhab→∈ (·upper₊ a₊ a⁻¹)
                  ∣ r · q , r⁻¹ , r·q∈upper , r⁻¹∈upper ,
                    alg-helper r q (>-arefl r>0) ∙ ·Assoc r q r⁻¹ ∣)
          (archimedes' a ε ε>0 q' (q₀ , q₀<r∈upper , q'<q₀))
