{-

Morphism between Ordered Field

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Algebra.OrderedField.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.MoreInts.QuoInt
  using    (ℤ)
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_)
open import Cubical.HITs.Rationals.QuoQ
  using (ℚ ; ℕ₊₁→ℤ ; _∼_)
  renaming (_+_ to _+ℚ_ ; _·_ to _·ℚ_)
open import Cubical.HITs.SetQuotients as SetQuot
open import Cubical.Relation.Nullary
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection

open import Classical.Preliminary.QuoInt
  using    (ℤOrder)
open import Classical.Preliminary.QuoQ
open import Classical.Algebra.OrderedRing.Morphism
open import Classical.Preliminary.CommRing.Instances.QuoQ
  renaming (ℚ to ℚRing)

open import Classical.Algebra.OrderedRing
open import Classical.Algebra.OrderedRing.Morphism
open import Classical.Algebra.OrderedField

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (a b c d b⁻¹ d⁻¹ : 𝓡 .fst)
      → (a · d + c · b) · (b⁻¹ · d⁻¹) ≡ (a · b⁻¹) · (d · d⁻¹) + (c · d⁻¹) · (b · b⁻¹)
    helper1 = solve 𝓡

    helper2 : (a c b⁻¹ d⁻¹ : 𝓡 .fst) → (a · b⁻¹) · 1r + (c · d⁻¹) · 1r ≡ a · b⁻¹ + c · d⁻¹
    helper2 = solve 𝓡

    helper3 : (a c b⁻¹ d⁻¹ : 𝓡 .fst) → (a · c) · (b⁻¹ · d⁻¹) ≡ (a · b⁻¹) · (c · d⁻¹)
    helper3 = solve 𝓡

    helper4 : (a d b⁻¹ d⁻¹ : 𝓡 .fst) → (a · b⁻¹) · (d · d⁻¹) ≡ ((a · d) · b⁻¹) · d⁻¹
    helper4 = solve 𝓡

    helper5 : (c b b⁻¹ d⁻¹ : 𝓡 .fst) → ((c · b) · b⁻¹) · d⁻¹ ≡ (c · d⁻¹) · (b · b⁻¹)
    helper5 = solve 𝓡


record OrderedFieldHom (𝒦 : OrderedField ℓ ℓ')(𝒦' : OrderedField ℓ'' ℓ''') : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
  field
    ordered-ring-hom : OrderedRingHom (𝒦 .fst) (𝒦' .fst)


module InclusionFromℚ (𝒦 : OrderedField ℓ ℓ') where

  open OrderStrOnCommRing

  open OrderedFieldStr 𝒦
  open InclusionFromℤ (𝒦 .fst)
  open OrderedRingStr  ℤOrder using () renaming (_>_ to _>ℤ_ ; >0≡>0r to >0≡>0r-ℤ)

  private
    K = 𝒦 .fst .fst .fst
    isSetK = is-set

  open Helpers (𝒦 .fst .fst)


  ℕ₊₁→ℤ>0 : (n : ℕ₊₁) → ℕ₊₁→ℤ n >ℤ 0
  ℕ₊₁→ℤ>0 (1+ n) = transport (>0≡>0r-ℤ (ℕ₊₁→ℤ (1+ n))) _

  ℕ₊₁→R : ℕ₊₁ → K
  ℕ₊₁→R n = ℤ→R (ℕ₊₁→ℤ n)

  ℕ₊₁→R>0 : (n : ℕ₊₁) → ℕ₊₁→R n > 0r
  ℕ₊₁→R>0 n = ℤ→R-Pres>0'' (ℕ₊₁→ℤ n) (ℕ₊₁→ℤ>0 n)

  ℕ₊₁→R≢0 : (n : ℕ₊₁) → ¬ ℕ₊₁→R n ≡ 0r
  ℕ₊₁→R≢0 n = >-arefl (ℕ₊₁→R>0 n)

  ℕ₊₁→ℤ-·₊₁-comm : (m n : ℕ₊₁) → ℕ₊₁→ℤ (m ·₊₁ n) ≡ (ℕ₊₁→ℤ m) ·ℤ (ℕ₊₁→ℤ n)
  ℕ₊₁→ℤ-·₊₁-comm (1+ m) (1+ n) = refl


  private

    module _ ((a , b) : ℤ × ℕ₊₁) where

      map-helper : K
      map-helper = ℤ→R a · inv (ℕ₊₁→R≢0 b)

      >0-helper' : a >ℤ 0 → map-helper > 0r
      >0-helper' a>0 = ·-Pres>0 (ℤ→R-Pres>0'' _ a>0) (p>0→p⁻¹>0 (ℕ₊₁→R>0 b))

      >0-helper : a >ℤ 0 → 𝒦 .fst .snd ._>0 map-helper
      >0-helper a>0 = transport (sym (>0≡>0r _)) (>0-helper' a>0)


    module _ ((a , b)(c , d) : ℤ × ℕ₊₁) where

      b≢0 = ℕ₊₁→R≢0 b
      d≢0 = ℕ₊₁→R≢0 d
      bd≢0 = ℕ₊₁→R≢0 (b ·₊₁ d)
      b⁻¹ = inv b≢0
      d⁻¹ = inv d≢0

      eq-helper : (r : (a , b) ∼ (c , d)) → map-helper (a , b) ≡ map-helper (c , d)
      eq-helper r = sym (·Rid _)
        ∙ (λ i → (ℤ→R a · b⁻¹) · ·-rInv d≢0 (~ i))
        ∙ helper4 _ _ _ _
        ∙ (λ i → (ℤ→R-Pres-· a (ℕ₊₁→ℤ d) (~ i) · b⁻¹) · d⁻¹)
        ∙ (λ i → (ℤ→R (r i) · b⁻¹) · d⁻¹)
        ∙ (λ i → (ℤ→R-Pres-· c (ℕ₊₁→ℤ b) i · b⁻¹) · d⁻¹)
        ∙ helper5 _ _ _ _
        ∙ (λ i → (ℤ→R c · d⁻¹) · ·-rInv b≢0 i)
        ∙ ·Rid _

      inv-path : inv (ℕ₊₁→R≢0 (b ·₊₁ d)) ≡ inv (·-≢0 b≢0 d≢0)
      inv-path i = inv-uniq {x≢0 = ℕ₊₁→R≢0 (b ·₊₁ d)} {y≢0 = ·-≢0 b≢0 d≢0}
        (cong ℤ→R (ℕ₊₁→ℤ-·₊₁-comm b d) ∙ ℤ→R-Pres-· _ _) i

      hom-helper : (a b c d : ℤ) → ℤ→R (a ·ℤ d +ℤ c ·ℤ b) ≡ ℤ→R a · ℤ→R d + ℤ→R c · ℤ→R b
      hom-helper a b c d = ℤ→R-Pres-+ _ _ ∙ (λ i → ℤ→R-Pres-· a d i + ℤ→R-Pres-· c b i)

      +-helper : map-helper (a ·ℤ ℕ₊₁→ℤ d +ℤ c ·ℤ ℕ₊₁→ℤ b , b ·₊₁ d) ≡ map-helper (a , b) + map-helper (c , d)
      +-helper = (λ i → hom-helper a (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ d) i · inv bd≢0)
        ∙ (λ i → (ℤ→R a · ℕ₊₁→R d + ℤ→R c · ℕ₊₁→R b) · inv-path i)
        ∙ (λ i → (ℤ→R a · ℕ₊₁→R d + ℤ→R c · ℕ₊₁→R b) · ·-Inv b≢0 d≢0 (~ i))
        ∙ helper1 _ _ _ _ _ _
        ∙ (λ i → (ℤ→R a · b⁻¹) · ·-rInv d≢0 i + (ℤ→R c · d⁻¹) · ·-rInv b≢0 i)
        ∙ helper2 _ _ _ _

      ·-helper : map-helper (a ·ℤ c , b ·₊₁ d) ≡ map-helper (a , b) · map-helper (c , d)
      ·-helper = (λ i → ℤ→R-Pres-· a c i · inv bd≢0)
        ∙ (λ i → (ℤ→R a · ℤ→R c) · inv-path i)
        ∙ (λ i → (ℤ→R a · ℤ→R c) · ·-Inv b≢0 d≢0 (~ i))
        ∙ helper3 _ _ _ _


  ℚ→K : ℚ → K
  ℚ→K =  SetQuot.elim (λ _ → isSetK) map-helper eq-helper

  ℚ→K-Pres-1 : ℚ→K 1 ≡ 1r
  ℚ→K-Pres-1 = ·-rInv _

  ℚ→K-Pres-+ : (p q : ℚ) → ℚ→K (p +ℚ q) ≡ ℚ→K p + ℚ→K q
  ℚ→K-Pres-+ = elimProp2 (λ _ _ → isSetK _ _) +-helper

  ℚ→K-Pres-· : (p q : ℚ) → ℚ→K (p ·ℚ q) ≡ ℚ→K p · ℚ→K q
  ℚ→K-Pres-· = elimProp2 (λ _ _ → isSetK _ _) ·-helper

  ℚ→K-Pres->0 : (p : ℚ) → ℚOrderedField .fst .snd ._>0 p → 𝒦 .fst .snd ._>0 (ℚ→K p)
  ℚ→K-Pres->0 = elimProp (λ _ → isPropΠ (λ _ → 𝒦 .fst .snd .isProp>0 _)) >0-helper


  {-

    (Ordered) Ring Homomorphism Instance

  -}

  isRingHomℚ→K : IsRingHom (CommRing→Ring ℚRing .snd) ℚ→K (CommRing→Ring (𝒦 .fst .fst) .snd)
  isRingHomℚ→K = makeIsRingHom ℚ→K-Pres-1 ℚ→K-Pres-+ ℚ→K-Pres-·

  ℚ→KCommRingHom : CommRingHom ℚRing (𝒦 .fst .fst)
  ℚ→KCommRingHom = _ , isRingHomℚ→K

  open OrderedRingHom

  ℚ→KOrderedRingHom : OrderedRingHom (ℚOrderedField .fst) (𝒦 .fst)
  ℚ→KOrderedRingHom .ring-hom = ℚ→KCommRingHom
  ℚ→KOrderedRingHom .pres->0  = ℚ→K-Pres->0
