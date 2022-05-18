{-

Properties of Ordered Field

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Classical.Algebra.OrderedField.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRingSolver.Reflection

open import Classical.Algebra.Field
open import Classical.Algebra.OrderedRing
open import Classical.Algebra.OrderedField.Base

private
  variable
    ℓ ℓ' ℓ'' : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (p q : 𝓡 .fst) → ((p + q) + (1r + 1r) · (- p)) ≡ q - p
    helper1 = solve 𝓡

    helper2 : (p p⁻¹ q⁻¹ : 𝓡 .fst) → p · (p⁻¹ · q⁻¹) ≡ (p · p⁻¹) · q⁻¹
    helper2 = solve 𝓡

    helper3 : (q p⁻¹ q⁻¹ : 𝓡 .fst) → q · (p⁻¹ · q⁻¹) ≡ (q · q⁻¹) · p⁻¹
    helper3 = solve 𝓡

    helper4 : (y z : 𝓡 .fst) → y + (z - y) ≡ z
    helper4 = solve 𝓡

    helper5 : (x y z : 𝓡 .fst) → x · (y · z) ≡ (y · x) · z
    helper5 = solve 𝓡


module OrderedFieldStr (𝒦 : OrderedField ℓ ℓ') where

  open FieldStr       (𝒦 .fst .fst , 𝒦 .snd) public
  open OrderedRingStr (𝒦 .fst) public

  private
    K = 𝒦 .fst .fst .fst

    variable
      p q x y z : K

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

  1/n>0 : (n : ℕ₊₁) →  1/ n > 0r
  1/n>0 (1+ n) = ·-lPosCancel>0 (ℕ→R-PosSuc>0 n) (subst (_> 0r) (sym (1/n·n≡1 (1+ n))) 1>0)


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

    Inverse of positive element

  -}

  inv₊ : q > 0r → K
  inv₊ q>0 = inv (>-arefl q>0)

  ·-rInv₊ : (q>0 : q > 0r) → q · inv₊ q>0 ≡ 1r
  ·-rInv₊ q>0 = 𝒦 .snd _ (>-arefl q>0) .snd

  ·-lInv₊ : (q>0 : q > 0r) → inv₊ q>0 · q ≡ 1r
  ·-lInv₊ q>0 = ·Comm _ _ ∙ ·-rInv₊ q>0


  {-

    Order of multiplicative inverse

  -}

  p>0→p⁻¹>0 : (p>0 : p > 0r) → inv₊ p>0 > 0r
  p>0→p⁻¹>0 {p = p} p>0 = ·-rPosCancel>0 {x = p} {y = inv₊ p>0} p>0 p·p⁻¹>0
    where p·p⁻¹>0 : p · inv₊ p>0 > 0r
          p·p⁻¹>0 = subst (_> 0r) (sym (·-rInv₊ p>0)) 1>0

  p>q>0→p·q⁻¹>1 : (q>0 : q > 0r) → p > q → p · inv₊ q>0 > 1r
  p>q>0→p·q⁻¹>1 {q = q} {p = p} q>0 p>q =
    subst (p · inv (>-arefl {x = q} q>0) >_) (·-rInv (>-arefl {x = q} q>0))
      (·-rPosPres< {x = inv (>-arefl {x = q} q>0)} {y = q} {z = p} (p>0→p⁻¹>0 {p = q} q>0) p>q)

  inv-Reverse< : (p>0 : p > 0r)(q>0 : q > 0r) → p > q → inv₊ p>0 < inv₊ q>0
  inv-Reverse< {p = p} {q = q} p>0 q>0 p>q = q⁻¹>p⁻¹
    where p⁻¹ = inv₊ p>0
          q⁻¹ = inv₊ q>0
          p⁻¹·q⁻¹>0 : p⁻¹ · q⁻¹ > 0r
          p⁻¹·q⁻¹>0 = ·-Pres>0 {x = p⁻¹} {y = q⁻¹} (p>0→p⁻¹>0 {p = p} p>0) (p>0→p⁻¹>0 {p = q} q>0)
          p·p⁻¹·q⁻¹>q·q⁻¹·p⁻¹ : (p · p⁻¹) · q⁻¹ > (q · q⁻¹) · p⁻¹
          p·p⁻¹·q⁻¹>q·q⁻¹·p⁻¹ = transport (λ i → helper2 p p⁻¹ q⁻¹ i > helper3 q p⁻¹ q⁻¹ i)
            (·-rPosPres< {x = p⁻¹ · q⁻¹} {y = q} {z = p} p⁻¹·q⁻¹>0 p>q)
          1·q⁻¹>1·p⁻¹ : 1r · q⁻¹ > 1r · p⁻¹
          1·q⁻¹>1·p⁻¹ = transport (λ i → ·-rInv₊ p>0 i · q⁻¹ > ·-rInv₊ q>0 i · p⁻¹) p·p⁻¹·q⁻¹>q·q⁻¹·p⁻¹
          q⁻¹>p⁻¹ : q⁻¹ > p⁻¹
          q⁻¹>p⁻¹ = transport (λ i → ·Lid q⁻¹ i > ·Lid p⁻¹ i) 1·q⁻¹>1·p⁻¹

  inv₊Idem : (q>0 : q > 0r) → inv₊ (p>0→p⁻¹>0 q>0) ≡ q
  inv₊Idem {q = q} q>0 = sym (·Lid _)
    ∙ (λ i → ·-rInv₊ q>0 (~ i) · inv₊ (p>0→p⁻¹>0 q>0))
    ∙ sym (·Assoc _ _ _) ∙ (λ i →  q · ·-rInv₊ (p>0→p⁻¹>0 q>0) i) ∙ ·Rid _


  private
    ·inv-helper : (y>0 : y > 0r) → (x · y) · inv₊ y>0 ≡ x
    ·inv-helper {x = x} y>0 = sym (·Assoc _ _ _) ∙ (λ i → x · ·-rInv₊ y>0 i) ∙ ·Rid _

  ·-MoveLToR< : (y>0 : y > 0r) → x · y < z → x < z · inv₊ y>0
  ·-MoveLToR< {y = y} {x = x} {z = z} y>0 xy<z =
    subst (_< z · inv₊ y>0) (·inv-helper y>0) (·-rPosPres< (p>0→p⁻¹>0 y>0) xy<z)

  ·-MoveRToL< : (y>0 : y > 0r) → z < x · y → z · inv₊ y>0 < x
  ·-MoveRToL< {y = y} {z = z} {x = x} y>0 xy>z =
    subst (_> z · inv₊ y>0) (·inv-helper y>0) (·-rPosPres< (p>0→p⁻¹>0 y>0) xy>z)


  {-

    Decomposition and ordering

  -}

  <-+-Decompose : (x y z : K) → x + y < z → Σ[ s ∈ K ] Σ[ t ∈ K ] (x < s) × (y < t) × (z ≡ s + t)
  <-+-Decompose x y z x+y<z = mid , z - mid , mid>x , z-mid>y , sym (helper4 mid z)
    where
    mid = middle x (z - y)
    x<z-y : x < z - y
    x<z-y = +-MoveLToR< x+y<z
    y+mid<z : y + mid < z
    y+mid<z = subst (y + mid <_) (helper4 y z) (+-lPres< (middle<r x<z-y))
    mid>x = middle>l x<z-y
    z-mid>y : y < z - mid
    z-mid>y = +-MoveLToR< y+mid<z


  private
    ·inv-helper' : (x>0 : x > 0r) → x · (y · inv₊ x>0) ≡ y
    ·inv-helper' {x = x} y>0 = helper5 _ _ _ ∙ ·inv-helper y>0

  <-·-Decompose : (x y z : K) → x > 0r → y > 0r → x · y < z
    → Σ[ s ∈ K ] Σ[ t ∈ K ] (x < s) × (y < t) × (z ≡ s · t)
  <-·-Decompose x y z x>0 y>0 xy<z =
    mid , z · inv₊ mid>0 , mid>x , z·mid⁻¹>y , sym (·inv-helper' mid>0)
    where
    mid = middle x (z · inv₊ y>0)
    x<zy⁻¹ : x < z · inv₊ y>0
    x<zy⁻¹ = ·-MoveLToR< y>0 xy<z
    mid>0 : mid > 0r
    mid>0 = <-trans x>0 (middle>l x<zy⁻¹)
    y·mid<z : y · mid < z
    y·mid<z = subst (y · mid <_) (·inv-helper' y>0) (·-lPosPres< y>0 (middle<r x<zy⁻¹))
    mid>x = middle>l x<zy⁻¹
    z·mid⁻¹>y : y < z · inv₊ mid>0
    z·mid⁻¹>y = ·-MoveLToR< mid>0 y·mid<z


  {-

    Pick out a smaller-than-both positive element

  -}

  min2 : x > 0r → y > 0r → Σ[ z ∈ K ] (z > 0r) × (z < x) × (z < y)
  min2 {x = x} {y = y} x>0 y>0 = case-split (trichotomy x y)
    where
    case-split : Trichotomy x y → Σ[ z ∈ K ] (z > 0r) × (z < x) × (z < y)
    case-split (lt x<y) = middle 0r x , middle>l x>0 , middle<r x>0 , <-trans (middle<r x>0) x<y
    case-split (gt x>y) = middle 0r y , middle>l y>0 , <-trans (middle<r y>0) x>y , middle<r y>0
    case-split (eq x≡y) =
      middle 0r x , middle>l x>0 , middle<r x>0 , subst (middle 0r x <_) x≡y (middle<r x>0)


{-

  Archimedean-ness of Ordered Field

-}

open import Classical.Preliminary.Nat
open import Classical.Algebra.OrderedRing.Archimedes

module _ (𝒦 : OrderedField ℓ ℓ')(archimedes : isArchimedean (𝒦 .fst)) where

  open OrderedFieldStr 𝒦

  private
    K = 𝒦 .fst .fst .fst

  -- An inverse version of Archimedean-ness,
  -- which says you can make a non-zero element arbitrarily small by dividing a natural number.

  isArchimedeanInv : Type (ℓ-max ℓ ℓ')
  isArchimedeanInv = (x ε : K) → x > 0r → ε > 0r → Σ[ n ∈ ℕ₊₁ ] ε / n < x

  isArchimedean→isArchimedeanInv : isArchimedeanInv
  isArchimedean→isArchimedeanInv x ε x>0 ε>0 = let (n , nx>ε) = archimedes ε x x>0 in helper n nx>ε
    where
    helper : (n : ℕ) → n ⋆ x > ε → Σ[ n ∈ ℕ₊₁ ] ε / n < x
    helper zero nx>ε = Empty.rec (<-asym ε>0 (subst (_> ε) (0⋆q≡0 _) nx>ε))
    helper (suc n) nx>ε = 1+ n ,
      subst (ε / (1+ n) <_) (sym (·Assoc _ _ _)
      ∙ ·-/-lInv x (1+ n)) (·-rPosPres< (1/n>0 (1+ n)) nx>ε)


  -- A useful lemma to lift mere existence to existence

  module _
    {P : (x : K) → Type ℓ''}
    (isPropP : (x : K) → isProp (P x))
    (decP : (x : K) → Dec (P x))
    (<-close : (x y : K) → x > 0r → x < y → P y → P x)
    (∃ε : ∥ Σ[ ε ∈ K ] (ε > 0r) × P ε ∥) where

    private
      P' : ℕ → Type ℓ''
      P' n = P (1r / (1+ n))

      1r/n>0 : (n : ℕ₊₁) → 1r / n > 0r
      1r/n>0 n = ·-Pres>0 1>0 (1/n>0 n)

      ∃P'n : ∥ Σ[ n ∈ ℕ ] P' n ∥
      ∃P'n = Prop.map
        (λ (ε , ε>0 , pε) →
          let (1+ n , 1/n<ε) =
                isArchimedean→isArchimedeanInv ε 1r ε>0 1>0
          in  n , <-close _ _ (1r/n>0 _) 1/n<ε pε) ∃ε

    findExplicit : Σ[ ε ∈ K ] (ε > 0r) × P ε
    findExplicit = let (n , p) = find (λ _ → isPropP _) (λ _ → decP _) ∃P'n in 1r / (1+ n) , (1r/n>0 _) , p
