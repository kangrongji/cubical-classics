{-



-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Algebra.OrderedField.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection

open import Classical.Algebra.Field
open import Classical.Algebra.OrderedRing
open import Classical.Algebra.OrderedField.Base

private
  variable
    ℓ ℓ' : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (p q : 𝓡 .fst) → ((p + q) + (1r + 1r) · (- p)) ≡ q - p
    helper1 = solve 𝓡

    helper2 : (p p⁻¹ q⁻¹ : 𝓡 .fst) → p · (p⁻¹ · q⁻¹) ≡ (p · p⁻¹) · q⁻¹
    helper2 = solve 𝓡

    helper3 : (q p⁻¹ q⁻¹ : 𝓡 .fst) → q · (p⁻¹ · q⁻¹) ≡ (q · q⁻¹) · p⁻¹
    helper3 = solve 𝓡


module OrderedFieldStr (𝒦 : OrderedField ℓ ℓ') where

  open FieldStr       (𝒦 .fst .fst , 𝒦 .snd) public
  open OrderedRingStr (𝒦 .fst) public

  private
    K = 𝒦 .fst .fst .fst

    variable
      p q : K

  open Helpers (𝒦 .fst .fst)


  {-

    Division by non-zero natural numbers

  -}

  1/_ : ℕ₊₁ → K
  1/ (1+ n) = inv {x = ℕ→R-Pos (suc n)} (>-arefl (ℕ→R-PosSuc>0 n))

  1/n·n≡1 : (n : ℕ₊₁) →  1/ n · ℕ→R-Pos (ℕ₊₁→ℕ n) ≡ 1r
  1/n·n≡1 (1+ n) = ·-lInv (>-arefl (ℕ→R-PosSuc>0 n))

  _/_ : K → ℕ₊₁ → K
  q / n = q · 1/ n

  ·-/-rInv : (q : K)(n : ℕ₊₁) → (q / n) · (ℕ→R-Pos (ℕ₊₁→ℕ n)) ≡ q
  ·-/-rInv q n = sym (·Assoc q _ _) ∙ (λ i → q · 1/n·n≡1 n i) ∙ ·Rid q

  ·-/-lInv : (q : K)(n : ℕ₊₁) → (ℕ→R-Pos (ℕ₊₁→ℕ n)) · (q / n) ≡ q
  ·-/-lInv q n = ·Comm _ (q / n) ∙ ·-/-rInv q n


  {-

    Middle of an interval

  -}

  middle : (p q : K) → K
  middle p q = (p + q) / 2

  middle-sym : (p q : K) → middle p q ≡ middle q p
  middle-sym p q i = (+Comm p q i) / 2

  2·middle : (p q : K) → 2r · middle p q ≡ p + q
  2·middle p q = ·-/-lInv (p + q) 2


  middle-l : (p q : K) → 2r · (middle p q - p) ≡ q - p
  middle-l p q = ·Rdist+ 2r (middle p q) _ ∙ (λ i → 2·middle p q i + 2r · (- p)) ∙ helper1 p q

  middle-r : (p q : K) → 2r · (middle p q - q) ≡ p - q
  middle-r p q = (λ i → 2r · (middle-sym p q i - q)) ∙ middle-l q p

  middle>l : p < q → middle p q > p
  middle>l {p = p} {q = q} p<q =
    Diff>0→> {x = middle p q} {y = p} (·-rPosCancel>0 {x = 2r} {y = middle p q - p} 2>0
      (subst (_> 0r) (sym (middle-l p q)) (>→Diff>0 {x = q} {y = p} p<q)))

  middle<r : p < q → q > middle p q
  middle<r {p = p} {q = q} p<q =
    Diff<0→< {x = middle p q} {y = q} (·-rPosCancel<0 {x = 2r} {y = middle p q - q} 2>0
      (subst (_< 0r) (sym (middle-r p q)) (<→Diff<0 {x = p} {y = q} p<q)))


  {-

    Order of multiplicative inverse

  -}

  p>0→p⁻¹>0 : (p>0 : p > 0r) → inv (>-arefl {x = p} p>0) > 0r
  p>0→p⁻¹>0 {p = p} p>0 = ·-rPosCancel>0 {x = p} {y = inv (>-arefl {x = p} p>0)} p>0 p·p⁻¹>0
    where p·p⁻¹>0 : p · inv (>-arefl {x = p} p>0) > 0r
          p·p⁻¹>0 = subst (_> 0r) (sym (·-rInv (>-arefl {x = p} p>0))) 1>0

  p>q>0→p·q⁻¹>1 : (q>0 : q > 0r) → p > q → p · inv (>-arefl {x = q} q>0) > 1r
  p>q>0→p·q⁻¹>1 {q = q} {p = p} q>0 p>q =
    subst (p · inv (>-arefl {x = q} q>0) >_) (·-rInv (>-arefl {x = q} q>0))
      (·-rPosPres< {x = inv (>-arefl {x = q} q>0)} {y = q} {z = p} (p>0→p⁻¹>0 {p = q} q>0) p>q)

  inv-Reverse< : (p>0 : p > 0r)(q>0 : q > 0r) → p > q → inv (>-arefl {x = p} p>0) < inv (>-arefl {x = q} q>0)
  inv-Reverse< {p = p} {q = q} p>0 q>0 p>q = q⁻¹>p⁻¹
    where p≢0 = >-arefl {x = p} p>0
          q≢0 = >-arefl {x = q} q>0
          p⁻¹ = inv p≢0
          q⁻¹ = inv q≢0
          p⁻¹·q⁻¹>0 : p⁻¹ · q⁻¹ > 0r
          p⁻¹·q⁻¹>0 = ·-Pres>0 {x = p⁻¹} {y = q⁻¹} (p>0→p⁻¹>0 {p = p} p>0) (p>0→p⁻¹>0 {p = q} q>0)
          p·p⁻¹·q⁻¹>q·q⁻¹·p⁻¹ : (p · p⁻¹) · q⁻¹ > (q · q⁻¹) · p⁻¹
          p·p⁻¹·q⁻¹>q·q⁻¹·p⁻¹ = transport (λ i → helper2 p p⁻¹ q⁻¹ i > helper3 q p⁻¹ q⁻¹ i)
            (·-rPosPres< {x = p⁻¹ · q⁻¹} {y = q} {z = p} p⁻¹·q⁻¹>0 p>q)
          1·q⁻¹>1·p⁻¹ : 1r · q⁻¹ > 1r · p⁻¹
          1·q⁻¹>1·p⁻¹ = transport (λ i → ·-rInv p≢0 i · q⁻¹ > ·-rInv q≢0 i · p⁻¹) p·p⁻¹·q⁻¹>q·q⁻¹·p⁻¹
          q⁻¹>p⁻¹ : q⁻¹ > p⁻¹
          q⁻¹>p⁻¹ = transport (λ i → ·Lid q⁻¹ i > ·Lid p⁻¹ i) 1·q⁻¹>1·p⁻¹
