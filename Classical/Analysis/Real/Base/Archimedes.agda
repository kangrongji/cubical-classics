{-

A Technical Lemma about Archimedean-ness

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Analysis.Real.Base.Archimedes where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (p q : 𝓡 .fst) → p + (q - p) ≡ q
    helper1 = solve 𝓡

    helper2 : (r u ε : 𝓡 .fst) → (r + ε) - u ≡ (r - u) + ε
    helper2 = solve 𝓡

    helper3 : (a b c : 𝓡 .fst) → (a - b) + (b - c) ≡ a - c
    helper3 = solve 𝓡

    helper4 : (b c : 𝓡 .fst) → c + (b - c) ≡ b
    helper4 = solve 𝓡


open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.Rationals.QuoQ using (ℚ)
open import Cubical.Relation.Nullary

open import Classical.Preliminary.QuoQ
open import Classical.Preliminary.QuoQ.Archimedes
  renaming (archimedes to archimedesℚ)
open import Classical.Preliminary.Nat
open import Classical.Algebra.Field
open import Classical.Algebra.OrderedRing
open import Classical.Axioms.ExcludedMiddle
open import Classical.Foundations.Powerset

open import Classical.Analysis.Real.Base.DedekindCut

open Helpers (ℚOrder .fst)


module Archimedes (decide : LEM) where

  open Powerset decide

  open Basics   decide
  open DedekindCut

  open FieldStr       ℚField
  open OrderedRingStr ℚOrder


  module _  (a : ℝ)(ε : ℚ)(ε>0 : ε > 0) where

    module _
      (p : ℚ)(¬p∈upper : ¬ p ∈ a .upper)
      where

      private
        P : ℕ → Type
        P n = (p + n ⋆ ε) ∈ a .upper

        isPropP : (n : ℕ) → isProp (P n)
        isPropP _ = isProp∈ (a .upper)

        decP : (n : ℕ) → Dec (P n)
        decP n = decide (isPropP n)

        ¬P0 : ¬ P zero
        ¬P0 p0 = ¬p∈upper (subst (_∈ a .upper) ((λ i → p + 0⋆q≡0 ε i) ∙ +Rid p) p0)

        ∃Pn : ∥ Σ[ n ∈ ℕ ] P n ∥
        ∃Pn = Prop.map
          (λ (q , q∈upper) →
            let (n , n·ε>q-p) = archimedesℚ (q - p) ε ε>0
                p+n·ε>q : p + n ⋆ ε > q
                p+n·ε>q = subst (p + n ⋆ ε >_) (helper1 p q) (+-lPres< {z = p} n·ε>q-p)
            in  n , a .upper-close _ _ q∈upper p+n·ε>q)
          (a .upper-inhab)

        interval : Σ[ n ∈ ℕ ] (¬ P n) × P (suc n)
        interval = findInterval isPropP decP ¬P0 ∃Pn

      archimedes'' : Σ[ r ∈ ℚ ] (¬ r ∈ a .upper) × (p ≤ r) × (r + ε) ∈ a .upper
      archimedes'' = _ , interval .snd .fst , +-rPos→≥ (n⋆q≥0 _ ε ε>0) ,
        subst (_∈ a .upper)
          ((λ i → p + sucn⋆q≡n⋆q+q (interval .fst) ε i) ∙ +Assoc _ _ _)
          (interval .snd .snd)


    module _
      (p : ℚ)(¬p∈upper : ¬ p ∈ a .upper)
      (q : ℚ)(q<p : q < p)
      where

      private
        min2 : (x y : ℚ) → x > 0 → y > 0 → Σ[ z ∈ ℚ ] (z > 0) × (z < x) × (z < y)
        min2 x y x>0 y>0 = case-split (trichotomy x y)
          where
          case-split : Trichotomy x y → Σ[ z ∈ ℚ ] (z > 0) × (z < x) × (z < y)
          case-split (lt x<y) = middle 0 x , middle>l x>0 , middle<r x>0 , <-trans (middle<r x>0) x<y
          case-split (gt x>y) = middle 0 y , middle>l y>0 , <-trans (middle<r y>0) x>y , middle<r y>0
          case-split (eq x≡y) =
            middle 0 x , middle>l x>0 , middle<r x>0 , subst (middle 0 x <_) x≡y (middle<r x>0)

        >-exchange : {a b c : ℚ} → a - b > c → a - c > b
        >-exchange {a = a} {b = b} {c = c} a-b>c =
          transport (λ i → helper3 a b c i > helper4 b c i) (+-rPres< {z = b - c} a-b>c)

      archimedes''' :
        ∥ Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ] (¬ s ∈ a .upper) × (q < r) × (r < s) × (r + ε) ∈ a .upper ∥
      archimedes''' =
        let (r , ¬r∈upper , p≤r , r+ε∈upper) = archimedes'' p ¬p∈upper in
        Prop.map
        (λ (t , t<r+ε , t∈upper) →
          let r-q = r - q
              r+ε-t = (r + ε) - t
              r-q>0 : r-q > 0
              r-q>0 = >→Diff>0 (<≤-trans q<p p≤r)
              r+ε-t>0 : r+ε-t > 0
              r+ε-t>0 = >→Diff>0 t<r+ε
              (u , u>0 , u<r-q , u<r+ε-t) = min2 r-q r+ε-t r-q>0 r+ε-t>0
              r+ε-u = (r + ε) - u
              r-u = r - u
              r-u+ε = (r - u) + ε
              r-u<r : r-u < r
              r-u<r = +-rNeg→< (-Reverse>0 u>0)
              r-u>q : r-u > q
              r-u>q = >-exchange u<r-q
              r-u+ε>t : r-u+ε > t
              r-u+ε>t = subst (_> t) (helper2 r u ε) (>-exchange u<r+ε-t)
          in  r-u , r , ¬r∈upper , r-u>q , r-u<r , a .upper-close _ _ t∈upper r-u+ε>t)
        (a .upper-round _ r+ε∈upper)


  archimedes' : (a : ℝ)(ε : ℚ)(ε>0 : ε > 0)
    → (p : ℚ)  → Σ[ s ∈ ℚ ] ((q : ℚ) → q ∈ a .upper → s < q) × (p < s)
    → ∥ Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ] ((q : ℚ) → q ∈ a .upper → s < q) × (p < r) × (r < s) × (r + ε) ∈ a .upper ∥
  archimedes' a ε ε>0 p (s , s<q∈upper , p<s) =
    Prop.map
    (λ (r , s , ¬s∈upper , q<r , r<s , r+ε∈upper) →
        r , s , ¬∈upper→<upper a _ ¬s∈upper , q<r , r<s , r+ε∈upper)
    (archimedes''' a ε ε>0 s (<upper→¬∈upper a _ s<q∈upper) p p<s)

  archimedes : (a : ℝ)(ε : ℚ)(ε>0 : ε > 0)
    → ∥ Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ] ((q : ℚ) → q ∈ a .upper → s < q) × (r < s) × (r + ε) ∈ a .upper ∥
  archimedes a ε ε>0 = Prop.rec squash
    (λ (q , q<r∈upper) → Prop.map
      (λ (r , s , s<t∈upper , p<r , r<s , r+ε∈upper) →
          r , s , s<t∈upper , r<s , r+ε∈upper)
      (archimedes' a ε ε>0 (q - 1) (q , q<r∈upper , q-1<q)))
    (a .lower-inhab)
