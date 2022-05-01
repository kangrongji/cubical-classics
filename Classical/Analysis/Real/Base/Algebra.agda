{-

The Real Number

-}
{-# OPTIONS --allow-unsolved-meta #-}
module Classical.Analysis.Real.Base.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.Rationals.QuoQ
open import Cubical.Relation.Nullary

open import Classical.Preliminary.Rational
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Analysis.Real.Base.DedekindCut


module ℝAlgebra (decide : LEM) where

  open Powerset decide
  open Real     decide

  open DedekindCut

  {-

    A Lemma about Archimedean-ness

  -}

  --archimedes : (a : ℝ)(ε : ℚ) → ∥ Σ[ r ∈ ℚ ] ((q : ℚ) → q ∈ a .upper → r < q) × (r + ε) ∈ a .upper ∥
  --archimedes = {!!}

  archimedes : (a : ℝ)(ε : ℚ)
    → ∥ Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ] ((q : ℚ) → q ∈ a .upper → s < q) × (r < s) × (r + ε) ∈ a .upper ∥
  archimedes = {!!}

  {-

    Addition

  -}

  +ℝ-Comm : (a b : ℝ) → a +ℝ b ≡ b +ℝ a
  +ℝ-Comm a b = ≤ℝ-asym (upper⊆ b a) (upper⊆ a b)
    where
    upper⊆ : (a b : ℝ){q : ℚ} → q ∈ (a +ℝ b) .upper → q ∈ (b +ℝ a) .upper
    upper⊆ a b {q = q} q∈upper = Inhab→∈ (+upper b a) (Prop.map
      (λ (s , t , s∈upper , t∈upper , q≡s+t) → t , s , t∈upper , s∈upper , q≡s+t ∙ +-comm s t)
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
          w∈upper , q≡s+t ∙ (λ i → s + t≡r+w i) ∙ +-assoc s r w)
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
          q≡s+t ∙ (λ i → s≡r+w i + t) ∙ sym (+-assoc r w t))
        (∈→Inhab (+upper a b) s∈upper))
      (∈→Inhab (+upper (a +ℝ b) c) q∈upper))


  +ℝ-rUnit : (a : ℝ) → a +ℝ 0 ≡ a
  +ℝ-rUnit a = ≤ℝ-asym upper⊇ upper⊆
    where
    upper⊆ : {q : ℚ} → q ∈ (a +ℝ 0) .upper → q ∈ a .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ (a .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s+t) →
        subst (_∈ a .upper) (sym q≡s+t)
          (a .upper-close (s + t) s s∈upper (<-+-pos (∈→Inhab (0 <P_) t∈upper))))
      (∈→Inhab (+upper a 0) q∈upper)

    upper⊇ : {q : ℚ} → q ∈ a .upper → q ∈ (a +ℝ 0) .upper
    upper⊇ {q = q} q∈upper = Prop.rec (isProp∈ ((a +ℝ 0) .upper))
      (λ (r , r<q , r∈upper) →
        Inhab→∈ (+upper a 0) ∣ r , q - r , r∈upper ,
        Inhab→∈ (0 <P_) (p>q→p-q>0 r<q) , helper q r ∣)
      (a .upper-round q q∈upper)
      where helper : (q r : ℚ) → q ≡ r + (q - r)
            helper = {!!}


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
              -p>-s = -reverse< p<s
              s+t>s-s : s + t > s - s
              s+t>s-s = <-trans (<-+ {r = s} -p>-s) (<-+ {r = s} t>-p)
              s+t>0 : s + t > 0
              s+t>0 = subst (s + t >_) (+-inverseʳ s) s+t>s-s
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
        subst (_∈ a .upper) (+-comm r q) r+q∈upper ,
        Inhab→∈ (-upper a) ∣ s , s<q∈upper , -reverse< r<s ∣ ,
        helper q r ∣)
      (archimedes a q)
      where helper : (q r : ℚ) → q ≡ (q + r) - r
            helper = {!!}

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
      (λ (s , t , s∈upper , t∈upper , q≡s·t) → t , s , t∈upper , s∈upper , q≡s·t ∙ ·-comm s t)
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
          w∈upper , q≡s·t ∙ (λ i → s · t≡r·w i) ∙ ·-assoc s r w)
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
          q≡s·t ∙ (λ i → s≡r·w i · t) ∙ sym (·-assoc r w t))
        (∈→Inhab (·upper₊ a b) s∈upper))
      (∈→Inhab (·upper₊ (a ·ℝ₊ b) c) q∈upper))


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
            p≢0 = q>0→q≢0 p>0
            p⁻¹ = inv p≢0 in
        Inhab→∈ (·upper₊ a 0₊) ∣ p , q · p⁻¹ , p∈upper ,
        Inhab→∈ (0 <P_) (>0-·-pos q>0 (p>0→p⁻¹>0 p>0)) , helper p q p≢0 ∣)
      (a .fst .upper-inhab)
      where helper : (p q : ℚ)(p≢0 : ¬ p ≡ 0) → q ≡ p · (q · inv p≢0)
            helper = {!!}


  ·ℝ₊-rUnit : (a : ℝ₊) → a ·ℝ₊ 1₊ ≡ a
  ·ℝ₊-rUnit a = path-ℝ₊ _ _ (≤ℝ-asym upper⊇ upper⊆)
    where
    upper⊆ : {q : ℚ} → q ∈ (a ·ℝ₊ 1₊) .fst .upper → q ∈ a .fst .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ (a .fst .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s·t) →
        let s>0 = q∈ℝ₊→q>0 a s s∈upper in
        subst (_∈ a .fst .upper) (sym q≡s·t)
          (a .fst .upper-close (s · t) s s∈upper (<-·-q>1 s>0 (∈→Inhab (1 <P_) t∈upper))))
      (∈→Inhab (·upper₊ a 1₊) q∈upper)

    upper⊇ : {q : ℚ} → q ∈ a .fst .upper → q ∈ (a ·ℝ₊ 1₊) .fst .upper
    upper⊇ {q = q} q∈upper = Prop.rec (isProp∈ ((a ·ℝ₊ 1₊) .fst .upper))
      (λ (r , r<q , r∈upper) →
        let r>0 = q∈ℝ₊→q>0 a r r∈upper
            r≢0 = q>0→q≢0 r>0
            r⁻¹ = inv r≢0 in
        Inhab→∈ (·upper₊ a 1₊) ∣ r , q · r⁻¹ , r∈upper ,
        Inhab→∈ (1 <P_) (p>q>0→p·q⁻¹>1 r>0 r<q) , helper q r r≢0 ∣)
      (a .fst .upper-round q q∈upper)
      where helper : (q r : ℚ)(r≢0 : ¬ r ≡ 0) → q ≡ r · (q · inv r≢0)
            helper = {!!}


  private
    take-distrib : (a : ℝ₊)(r w u v : ℚ)
      → r ∈ a .fst .upper → u ∈ a .fst .upper → w > 0 → v > 0
      → Σ[ x ∈ ℚ ] (x ∈ a .fst .upper) × (x · (w + v) < (r · w) + (u · v))
    take-distrib a r w u v r∈upper u∈upper w>0 v>0 =
      case trichotomy< r u
      return (λ _ → Σ[ x ∈ ℚ ] (x ∈ a .fst .upper) × (x · (w + v) < (r · w) + (u · v))) of λ
      { (lt r<u) → u , u∈upper , {!!}
      ; (eq r≡u) → u , u∈upper , {!!}
      ; (gt r>u) → r , r∈upper , {!!} }


  ·ℝ₊-lDistrib : (a b c : ℝ₊) → (a ·ℝ₊ b) +ℝ₊ (a ·ℝ₊ c) ≡ a ·ℝ₊ (b +ℝ₊ c)
  ·ℝ₊-lDistrib a b c = path-ℝ₊ _ _ (≤ℝ-asym upper⊇ upper⊆)
    where
    upper⊆ : {q : ℚ} → q ∈ ((a ·ℝ₊ b) +ℝ₊ (a ·ℝ₊ c)) .fst .upper → q ∈ (a ·ℝ₊ (b +ℝ₊ c)) .fst .upper
    upper⊆ {q = q} q∈upper = Prop.rec (isProp∈ ((a ·ℝ₊ (b +ℝ₊ c)) .fst .upper))
      (λ (s , t , s∈upper , t∈upper , q≡s+t) →
        Prop.rec2 (isProp∈ ((a ·ℝ₊ (b +ℝ₊ c)) .fst .upper))
        (λ (r , w , r∈upper , w∈upper , s≡r·w)
           (u , v , u∈upper , v∈upper , t≡u·v) →
          let (x , x∈upper , x·[w+v]<[r·w]+[u·v]) =
                take-distrib a r w u v r∈upper u∈upper
                (q∈ℝ₊→q>0 b w w∈upper) (q∈ℝ₊→q>0 c v v∈upper)
              x·[w+v]∈upper : x · (w + v) ∈ (a ·ℝ₊ (b +ℝ₊ c)) .fst .upper
              x·[w+v]∈upper = Inhab→∈ (·upper₊ a (b +ℝ₊ c))
                ∣ x , w + v , x∈upper ,
                  Inhab→∈ (+upper₊ b c) ∣ w , v , w∈upper , v∈upper , refl ∣ , refl ∣
              [r·w]+[u·v]≡q : (r · w) + (u · v) ≡ q
              [r·w]+[u·v]≡q = (λ i → s≡r·w (~ i) + t≡u·v (~ i)) ∙ sym q≡s+t
              x·[w+v]<q : x · (w + v) < q
              x·[w+v]<q = subst (x · (w + v) <_) [r·w]+[u·v]≡q x·[w+v]<[r·w]+[u·v]
          in  (a ·ℝ₊ (b +ℝ₊ c)) .fst .upper-close _ _ x·[w+v]∈upper x·[w+v]<q)
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
          q≡s·t ∙ cong (s ·_) t≡r+w ∙ sym (·-distribˡ s r w))
        (∈→Inhab (+upper₊ b c) t∈upper))
      (∈→Inhab (·upper₊ a (b +ℝ₊ c)) q∈upper))


  {-

    Multiplicative Inverse

  -}

  --isFieldℝ : (a : ℝ) → ¬ a ≡ 0 → {!!}
  --isFieldℝ = {!!} -}



  {-

    Absolute Value

  -}

  -0≡0 : -ℝ 0 ≡ 0
  -0≡0 = sym (+ℝ-rUnit (-ℝ 0)) ∙ +ℝ-lInverse 0

  absℝ : ℝ → ℝ₊
  absℝ a with dichotomyℝ a 0
  ... | ge a≥0 = a , a≥0
  ... | lt a<0 = -ℝ a , subst (_≤ℝ (-ℝ a)) -0≡0 (<ℝ-reverse a 0 a<0)
