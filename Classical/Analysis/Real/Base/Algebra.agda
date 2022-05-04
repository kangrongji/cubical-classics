{-

The Real Number

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Analysis.Real.Base.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
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


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.Rationals.QuoQ using (ℚ)
open import Cubical.Relation.Nullary

open import Classical.Preliminary.QuoQ
open import Classical.Algebra.Field
open import Classical.Algebra.OrderedRing
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Analysis.Real.Base.DedekindCut
open import Classical.Analysis.Real.Base.Archimedes


open Helpers (ℚOrder .fst)


module Algebra (decide : LEM) where

  open Powerset   decide

  open Basics     decide
  open Archimedes decide
  open DedekindCut

  open FieldStr       ℚField
  open OrderedRingStr ℚOrder


  {-

    Addition

  -}

  +ℝ-Comm : (a b : ℝ) → a +ℝ b ≡ b +ℝ a
  +ℝ-Comm a b = ≤ℝ-asym (upper⊆ b a) (upper⊆ a b)
    where
    upper⊆ : (a b : ℝ){q : ℚ} → q ∈ (a +ℝ b) .upper → q ∈ (b +ℝ a) .upper
    upper⊆ a b {q = q} q∈upper = Inhab→∈ (+upper b a) (Prop.map
      (λ (s , t , s∈upper , t∈upper , q≡s+t) → t , s , t∈upper , s∈upper , q≡s+t ∙ +Comm s t)
      (∈→Inhab (+upper a b) q∈upper))


  +ℝ-Assoc : (a b c : ℝ) → a +ℝ (b +ℝ c) ≡ (a +ℝ b) +ℝ c
  +ℝ-Assoc a b c = ≤ℝ-asym upper⊇ upper⊆
    where
    upper⊆ : {q : ℚ} → q ∈ (a +ℝ (b +ℝ c)) .upper → q ∈ ((a +ℝ b) +ℝ c) .upper
    upper⊆ {q = q} q∈upper = Inhab→∈ (+upper (a +ℝ b) c)
      (Prop.rec squash
      (λ (s , t , s∈upper , t∈upper , q≡s+t) →
        Prop.map
        (λ (r , w , r∈upper , w∈upper , t≡r+w) →
          s + r , w ,
          Inhab→∈ (+upper a b) ∣ s , r , s∈upper , r∈upper , refl ∣ ,
          w∈upper , q≡s+t ∙ (λ i → s + t≡r+w i) ∙ +Assoc s r w)
        (∈→Inhab (+upper b c) t∈upper))
      (∈→Inhab (+upper a (b +ℝ c)) q∈upper))

    upper⊇ : {q : ℚ} → q ∈ ((a +ℝ b) +ℝ c) .upper → q ∈ (a +ℝ (b +ℝ c)) .upper
    upper⊇ {q = q} q∈upper = Inhab→∈ (+upper a (b +ℝ c))
      (Prop.rec squash
      (λ (s , t , s∈upper , t∈upper , q≡s+t) →
        Prop.map
        (λ (r , w , r∈upper , w∈upper , s≡r+w) →
          r , w + t ,
          r∈upper , Inhab→∈ (+upper b c) ∣ w , t , w∈upper , t∈upper , refl ∣ ,
          q≡s+t ∙ (λ i → s≡r+w i + t) ∙ sym (+Assoc r w t))
        (∈→Inhab (+upper a b) s∈upper))
      (∈→Inhab (+upper (a +ℝ b) c) q∈upper))


  +ℝ-rUnit : (a : ℝ) → a +ℝ 0 ≡ a
  +ℝ-rUnit a = ≤ℝ-asym upper⊇ upper⊆
    where
    upper⊆ : {q : ℚ} → q ∈ (a +ℝ 0) .upper → q ∈ a .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ (a .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s+t) →
        subst (_∈ a .upper) (sym q≡s+t)
          (a .upper-close (s + t) s s∈upper (+-rPos→> (∈→Inhab (0 <P_) t∈upper))))
      (∈→Inhab (+upper a 0) q∈upper)

    upper⊇ : {q : ℚ} → q ∈ a .upper → q ∈ (a +ℝ 0) .upper
    upper⊇ {q = q} q∈upper = Prop.rec (isProp∈ ((a +ℝ 0) .upper))
      (λ (r , r<q , r∈upper) →
        Inhab→∈ (+upper a 0) ∣ r , q - r , r∈upper ,
        Inhab→∈ (0 <P_) (>→Diff>0 r<q) , helper1 q r ∣)
      (a .upper-round q q∈upper)


  +ℝ-rInverse : (a : ℝ) → a +ℝ (-ℝ a) ≡ 0
  +ℝ-rInverse a = ≤ℝ-asym upper⊇ upper⊆
    where
    upper⊆ : {q : ℚ} → q ∈ (a +ℝ (-ℝ a)) .upper → q ∈ 0 .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ (0 .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s+t) → Prop.rec (isProp∈ (0 .upper))
        (λ (p , p<r∈upper , t>-p) →
          let p<s : p < s
              p<s = p<r∈upper s s∈upper
              -p>-s : - p > - s
              -p>-s = -Reverse< p<s
              s+t>s-s : s + t > s - s
              s+t>s-s = <-trans (+-lPres< {z = s} -p>-s) (+-lPres< {z = s} t>-p)
              s+t>0 : s + t > 0
              s+t>0 = subst (s + t >_) (+Rinv s) s+t>s-s
              q>0 : q > 0
              q>0 = subst (_> 0) (sym q≡s+t) s+t>0
          in  Inhab→∈ (0 <P_) q>0)
        (∈→Inhab (-upper a) t∈upper))
      (∈→Inhab (+upper a (-ℝ a)) q∈upper)

    upper⊇ : {q : ℚ} → q ∈ 0 .upper → q ∈ (a +ℝ (-ℝ a)) .upper
    upper⊇ {q = q} q∈upper =
      let q>0 = ∈→Inhab (0 <P_) q∈upper in
      Prop.rec (isProp∈ ((a +ℝ (-ℝ a)) .upper))
      (λ (r , s , s<q∈upper , r<s , r+q∈upper) →
        Inhab→∈ (+upper a (-ℝ a)) ∣ q + r , - r ,
        subst (_∈ a .upper) (+Comm r q) r+q∈upper ,
        Inhab→∈ (-upper a) ∣ s , s<q∈upper , -Reverse< r<s ∣ ,
        helper2 q r ∣)
      (archimedes a q q>0)


  +ℝ-lUnit : (a : ℝ) → 0 +ℝ a ≡ a
  +ℝ-lUnit a = +ℝ-Comm 0 a ∙ +ℝ-rUnit a

  +ℝ-lInverse : (a : ℝ) → (-ℝ a) +ℝ a ≡ 0
  +ℝ-lInverse a = +ℝ-Comm (-ℝ a) a ∙ +ℝ-rInverse a

  -ℝ-Involutive : (a : ℝ) → -ℝ (-ℝ a) ≡ a
  -ℝ-Involutive a =
      sym (+ℝ-rUnit (-ℝ (-ℝ a)))
    ∙ (λ i → (-ℝ (-ℝ a)) +ℝ (+ℝ-lInverse a (~ i)))
    ∙ +ℝ-Assoc (-ℝ (-ℝ a)) (-ℝ a) a
    ∙ (λ i → (+ℝ-lInverse (-ℝ a) i) +ℝ a)
    ∙ +ℝ-lUnit a

  {-

    Multiplication of Non-Negative Reals

  -}

  ·ℝ₊-Comm : (a b : ℝ₊) → a ·ℝ₊ b ≡ b ·ℝ₊ a
  ·ℝ₊-Comm a b = path-ℝ₊ _ _ (≤ℝ-asym (upper⊆ b a) (upper⊆ a b))
    where
    upper⊆ : (a b : ℝ₊){q : ℚ} → q ∈ (a ·ℝ₊ b) .fst .upper → q ∈ (b ·ℝ₊ a) .fst .upper
    upper⊆ (a , a≥0) (b , b≥0) {q = q} q∈upper = Inhab→∈ (·upper b a) (Prop.map
      (λ (s , t , s∈upper , t∈upper , q≡s·t) → t , s , t∈upper , s∈upper , q≡s·t ∙ ·Comm s t)
      (∈→Inhab (·upper a b) q∈upper))


  ·ℝ₊-Assoc : (a b c : ℝ₊) → a ·ℝ₊ (b ·ℝ₊ c) ≡ (a ·ℝ₊ b) ·ℝ₊ c
  ·ℝ₊-Assoc a b c = path-ℝ₊ _ _ (≤ℝ-asym upper⊇ upper⊆)
    where
    upper⊆ : {q : ℚ} → q ∈ (a ·ℝ₊ (b ·ℝ₊ c)) .fst .upper → q ∈ ((a ·ℝ₊ b) ·ℝ₊ c) .fst .upper
    upper⊆ {q = q} q∈upper = Inhab→∈ (·upper₊ (a ·ℝ₊ b) c)
      (Prop.rec squash
      (λ (s , t , s∈upper , t∈upper , q≡s·t) →
        Prop.map
        (λ (r , w , r∈upper , w∈upper , t≡r·w) →
          s · r , w ,
          Inhab→∈ (·upper₊ a b) ∣ s , r , s∈upper , r∈upper , refl ∣ ,
          w∈upper , q≡s·t ∙ (λ i → s · t≡r·w i) ∙ ·Assoc s r w)
        (∈→Inhab (·upper₊ b c) t∈upper))
      (∈→Inhab (·upper₊ a (b ·ℝ₊ c)) q∈upper))

    upper⊇ : {q : ℚ} → q ∈ ((a ·ℝ₊ b) ·ℝ₊ c) .fst .upper → q ∈ (a ·ℝ₊ (b ·ℝ₊ c)) .fst .upper
    upper⊇ {q = q} q∈upper = Inhab→∈ (·upper₊ a (b ·ℝ₊ c))
      (Prop.rec squash
      (λ (s , t , s∈upper , t∈upper , q≡s·t) →
        Prop.map
        (λ (r , w , r∈upper , w∈upper , s≡r·w) →
          r , w · t ,
          r∈upper , Inhab→∈ (·upper₊ b c) ∣ w , t , w∈upper , t∈upper , refl ∣ ,
          q≡s·t ∙ (λ i → s≡r·w i · t) ∙ sym (·Assoc r w t))
        (∈→Inhab (·upper₊ a b) s∈upper))
      (∈→Inhab (·upper₊ (a ·ℝ₊ b) c) q∈upper))


  private
    alg-helper : (p q : ℚ)(p≢0 : ¬ p ≡ 0) → q ≡ p · (q · inv p≢0)
    alg-helper p q p≢0 = sym (·Rid q) ∙ (λ i → q · ·-rInv p≢0 (~ i)) ∙ helper3 p q (inv p≢0)


  ·ℝ₊-rZero : (a : ℝ₊) → a ·ℝ₊ 0₊ ≡ 0₊
  ·ℝ₊-rZero a = path-ℝ₊ _ _ (≤ℝ-asym upper⊇ upper⊆)
    where
    upper⊆ : {q : ℚ} → q ∈ (a ·ℝ₊ 0₊) .fst .upper → q ∈ 0 .upper
    upper⊆ = (a ·ℝ₊ 0₊) .snd

    upper⊇ : {q : ℚ} → q ∈ 0 .upper → q ∈ (a ·ℝ₊ 0₊) .fst .upper
    upper⊇ {q = q} q∈upper = Prop.rec (isProp∈ ((a ·ℝ₊ 0₊) .fst .upper))
      (λ (p , p∈upper) →
        let q>0 = ∈→Inhab (0 <P_) q∈upper
            p>0 = q∈ℝ₊→q>0 a p p∈upper
            p≢0 = >-arefl p>0
            p⁻¹ = inv p≢0 in
        Inhab→∈ (·upper₊ a 0₊) ∣ p , q · p⁻¹ , p∈upper ,
        Inhab→∈ (0 <P_) (·-Pres>0 q>0 (p>0→p⁻¹>0 p>0)) , alg-helper p q p≢0 ∣)
      (a .fst .upper-inhab)


  ·ℝ₊-rUnit : (a : ℝ₊) → a ·ℝ₊ 1₊ ≡ a
  ·ℝ₊-rUnit a = path-ℝ₊ _ _ (≤ℝ-asym upper⊇ upper⊆)
    where
    upper⊆ : {q : ℚ} → q ∈ (a ·ℝ₊ 1₊) .fst .upper → q ∈ a .fst .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ (a .fst .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s·t) →
        let s>0 = q∈ℝ₊→q>0 a s s∈upper in
        subst (_∈ a .fst .upper) (sym q≡s·t)
          (a .fst .upper-close (s · t) s s∈upper (·-Pos·>1→> s>0 (∈→Inhab (1 <P_) t∈upper))))
      (∈→Inhab (·upper₊ a 1₊) q∈upper)

    upper⊇ : {q : ℚ} → q ∈ a .fst .upper → q ∈ (a ·ℝ₊ 1₊) .fst .upper
    upper⊇ {q = q} q∈upper = Prop.rec (isProp∈ ((a ·ℝ₊ 1₊) .fst .upper))
      (λ (r , r<q , r∈upper) →
        let r>0 = q∈ℝ₊→q>0 a r r∈upper
            r≢0 = >-arefl r>0
            r⁻¹ = inv r≢0 in
        Inhab→∈ (·upper₊ a 1₊) ∣ r , q · r⁻¹ , r∈upper ,
        Inhab→∈ (1 <P_) (p>q>0→p·q⁻¹>1  r>0 r<q) , alg-helper r q r≢0 ∣)
      (a .fst .upper-round q q∈upper)


  private
    upper-round2 : (a : ℝ)(p q : ℚ) → p ∈ a .upper → q ∈ a .upper → ∥ Σ[ r ∈ ℚ ] (r < p) × (r < q) × (r ∈ a .upper) ∥
    upper-round2 a p q p∈upper q∈upper = Prop.map2
      (λ (r , r<p , r∈upper) (s , s<q , s∈upper) →
        case trichotomy r s of λ
        { (lt r<s) → r , r<p , <-trans r<s s<q , r∈upper
        ; (eq r≡s) → s , subst (_< p) r≡s r<p , s<q , s∈upper
        ; (gt r>s) → s , <-trans r>s r<p , s<q , s∈upper })
      (a .upper-round p p∈upper)
      (a .upper-round q q∈upper)

  ·ℝ₊-lDistrib : (a b c : ℝ₊) → (a ·ℝ₊ b) +ℝ₊ (a ·ℝ₊ c) ≡ a ·ℝ₊ (b +ℝ₊ c)
  ·ℝ₊-lDistrib a b c = path-ℝ₊ _ _ (≤ℝ-asym upper⊇ upper⊆)
    where
    upper⊆ : {q : ℚ} → q ∈ ((a ·ℝ₊ b) +ℝ₊ (a ·ℝ₊ c)) .fst .upper → q ∈ (a ·ℝ₊ (b +ℝ₊ c)) .fst .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ ((a ·ℝ₊ (b +ℝ₊ c)) .fst .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s+t) →
        Prop.rec2 (isProp∈ ((a ·ℝ₊ (b +ℝ₊ c)) .fst .upper))
        (λ (r , w , r∈upper , w∈upper , s≡r·w)
           (u , v , u∈upper , v∈upper , t≡u·v) →
          Prop.rec (isProp∈ ((a ·ℝ₊ (b +ℝ₊ c)) .fst .upper))
          (λ (x , x<r , x<u , x∈upper) →
            let x>0 = q∈ℝ₊→q>0 a x x∈upper
                w>0 = q∈ℝ₊→q>0 b w w∈upper
                v>0 = q∈ℝ₊→q>0 c v v∈upper
                x·w+x·v<r·w+u·v : (x · w) + (x · v) < (r · w) + (u · v)
                x·w+x·v<r·w+u·v = +-Pres< (·-rPosPres< w>0 x<r) (·-rPosPres< v>0 x<u)
                x·[w+v]<r·w+u·v : x · (w + v) < (r · w) + (u · v)
                x·[w+v]<r·w+u·v = subst (_< ((r · w) + (u · v))) (sym (·Rdist+ x w v)) x·w+x·v<r·w+u·v
                x·[w+v]∈upper : x · (w + v) ∈ (a ·ℝ₊ (b +ℝ₊ c)) .fst .upper
                x·[w+v]∈upper = Inhab→∈ (·upper₊ a (b +ℝ₊ c))
                  ∣ x , w + v , x∈upper ,
                    Inhab→∈ (+upper₊ b c) ∣ w , v , w∈upper , v∈upper , refl ∣ , refl ∣
                r·w+u·v≡q : (r · w) + (u · v) ≡ q
                r·w+u·v≡q = (λ i → s≡r·w (~ i) + t≡u·v (~ i)) ∙ sym q≡s+t
                x·[w+v]<q : x · (w + v) < q
                x·[w+v]<q = subst (x · (w + v) <_) r·w+u·v≡q x·[w+v]<r·w+u·v
            in  (a ·ℝ₊ (b +ℝ₊ c)) .fst .upper-close _ _ x·[w+v]∈upper x·[w+v]<q)
            (upper-round2 (a .fst) r u r∈upper u∈upper))
        (∈→Inhab (·upper₊ a b) s∈upper)
        (∈→Inhab (·upper₊ a c) t∈upper))
      (∈→Inhab (+upper₊ (a ·ℝ₊ b) (a ·ℝ₊ c)) q∈upper)

    upper⊇ : {q : ℚ} → q ∈ (a ·ℝ₊ (b +ℝ₊ c)) .fst .upper → q ∈ ((a ·ℝ₊ b) +ℝ₊ (a ·ℝ₊ c)) .fst .upper
    upper⊇ {q = q} q∈upper = Inhab→∈ (+upper₊ (a ·ℝ₊ b) (a ·ℝ₊ c))
      (Prop.rec squash
      (λ (s , t , s∈upper , t∈upper , q≡s·t) →
        Prop.map
        (λ (r , w , r∈upper , w∈upper , t≡r+w) →
          s · r , s · w ,
          Inhab→∈ (·upper₊ a b) ∣ s , r , s∈upper , r∈upper , refl ∣ ,
          Inhab→∈ (·upper₊ a c) ∣ s , w , s∈upper , w∈upper , refl ∣ ,
          q≡s·t ∙ cong (s ·_) t≡r+w ∙ ·Rdist+ s r w)
        (∈→Inhab (+upper₊ b c) t∈upper))
      (∈→Inhab (·upper₊ a (b +ℝ₊ c)) q∈upper))


  -- Multiplicative Inverse

  module _
    (a₊@(a , a≥0) : ℝ₊)(q₀ : ℚ)(q₀>0 : q₀ > 0)
    (q₀<r∈upper : ((r : ℚ) → r ∈ a .upper → q₀ < r)) where

    private
      a⁻¹ : ℝ₊
      a⁻¹ = invℝ₊ a q₀ q₀>0 q₀<r∈upper

      a·a⁻¹ = (a₊ ·ℝ₊ a⁻¹) .fst

      ineq-helper : (r q q' : ℚ) → q - 1 > 0 → r > q' → r + (q' · (q - 1)) < r · q
      ineq-helper r q q' q-1>0 r>q' = subst (r + (q' · (q - 1)) <_) (helper4 q r) r+·<r+·
        where r+·<r+· : r + (q' · (q - 1)) < r + (r · (q - 1))
              r+·<r+· = +-lPres< (·-rPosPres< q-1>0 r>q')

    ·ℝ₊-rInv : a·a⁻¹ ≡ 1
    ·ℝ₊-rInv = ≤ℝ-asym upper⊇ upper⊆
      where
      upper⊆ : {q : ℚ} → q ∈ a·a⁻¹ .upper → q ∈ 1 .upper
      upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ (1 .upper))
        (λ (s , t , s∈upper , t∈upper , q≡s·t) → Prop.rec (isProp∈ (1 .upper))
          (λ (p , p>0 , p<r∈upper , t>p⁻¹) →
            let p<s : p < s
                p<s = p<r∈upper s s∈upper
                s>0 : s > 0
                s>0 = <-trans q₀>0 (q₀<r∈upper s s∈upper)
                p⁻¹ = inv (>-arefl p>0)
                s⁻¹ = inv (>-arefl s>0)
                p⁻¹>s⁻¹ : p⁻¹ > s⁻¹
                p⁻¹>s⁻¹ = inv-Reverse< s>0 p>0 p<s
                s·t>s·s⁻¹ : s · t > s · s⁻¹
                s·t>s·s⁻¹ = <-trans (·-lPosPres< {x = s} s>0 p⁻¹>s⁻¹) (·-lPosPres< {x = s} s>0 t>p⁻¹)
                s·t>1 : s · t > 1
                s·t>1 = subst (s · t >_) (·-rInv (>-arefl s>0)) s·t>s·s⁻¹
                q>1 : q > 1
                q>1 = subst (_> 1) (sym q≡s·t) s·t>1
            in  Inhab→∈ (1 <P_) q>1)
          (∈→Inhab (inv-upper a) t∈upper))
        (∈→Inhab (·upper₊ a₊ a⁻¹) q∈upper)

      upper⊇ : {q : ℚ} → q ∈ 1 .upper → q ∈ a·a⁻¹ .upper
      upper⊇ {q = q} q∈upper =
        let q>1 = ∈→Inhab (1 <P_) q∈upper
            q-1>0 : q - 1 > 0
            q-1>0 = subst (q - 1 >_) (+Rinv 1) (+-rPres< {z = - 1} q>1)
            q' = middle 0 q₀
            q'>0 : q' > 0
            q'>0 = middle>l q₀>0
            q'<q₀ : q' < q₀
            q'<q₀ = middle<r q₀>0
            ε = q' · (q - 1)
            ε>0 : ε > 0
            ε>0 = ·-Pres>0 q'>0 q-1>0 in
        Prop.rec (isProp∈ (a·a⁻¹ .upper))
          (λ (r , s , s<q∈upper , q'<r , r<s , r+ε∈upper) →
            let r+ε<r·q : r + ε < r · q
                r+ε<r·q = ineq-helper r q q' q-1>0 q'<r
                r·q∈upper : r · q ∈ a .upper
                r·q∈upper = a .upper-close _ _ r+ε∈upper r+ε<r·q
                r>0 : r > 0
                r>0 = <-trans q'>0 q'<r
                r⁻¹ = inv (>-arefl r>0)
                s>0 : s > 0
                s>0 = <-trans r>0 r<s
                r⁻¹∈upper : r⁻¹ ∈ a⁻¹ .fst .upper
                r⁻¹∈upper = Inhab→∈ (inv-upper a)
                  ∣ s , s>0 , s<q∈upper , inv-Reverse< s>0 r>0 r<s ∣
            in  Inhab→∈ (·upper₊ a₊ a⁻¹)
                  ∣ r · q , r⁻¹ , r·q∈upper , r⁻¹∈upper ,
                    alg-helper r q (>-arefl r>0) ∙ ·Assoc r q r⁻¹ ∣)
          (archimedes' a ε ε>0 q' (q₀ , q₀<r∈upper , q'<q₀))
