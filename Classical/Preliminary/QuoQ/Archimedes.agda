{-

  Archimedean-ness of ℚ

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.QuoQ.Archimedes where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (n c b : 𝓡 .fst) → n · (c · b) ≡ (n · c) · (1r · b)
    helper1 = solve 𝓡

    helper2 : (n : 𝓡 .fst) → (1r + n) · (1r · 1r) ≡ (1r · 1r + n · 1r) · (1r · 1r)
    helper2 = solve 𝓡

    helper3 : (n q : 𝓡 .fst) → (1r + n) · q ≡ (n · q) + q
    helper3 = solve 𝓡


open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
  using    (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.MoreInts.QuoInt
  using    (ℤ ; pos)
  renaming (_·_ to _·ℤ_ ; _+_ to _+ℤ_ ; -_ to -ℤ_)
open import Cubical.HITs.Rationals.QuoQ
  using    (ℚ ; ℕ₊₁→ℤ ; ·-zeroˡ ; ·-identityˡ)
open import Cubical.HITs.SetQuotients as SetQuot
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Classical.Preliminary.QuoInt
  using    (ℤOrder ; ℕ₊₁→ℤ>0)
  renaming (archimedes' to archimedesℤ)
open import Classical.Preliminary.QuoQ.Order
  using    (ℚOrder)
open import Classical.Preliminary.Nat
open import Classical.Algebra.OrderedRing


open CommRingStr    (ℚOrder .fst .snd)
open OrderedRingStr  ℚOrder

open OrderedRingStr  ℤOrder
  using    ()
  renaming (_<_ to _<ℤ_ ; _>_ to _>ℤ_
           ; ·-Pres>0 to ·ℤ-Pres>0)

open Helpers (ℤOrder .fst)
open Helpers (ℚOrder .fst) using () renaming (helper3 to helper3ℚ)


-- Direct multiplication by natural numbers

_⋆_ : ℕ → ℚ → ℚ
n ⋆ q = [ pos n , 1 ] · q

0⋆q≡0 : (q : ℚ) → 0 ⋆ q ≡ 0
0⋆q≡0 q = ·-zeroˡ q

1⋆q≡q : (q : ℚ) → 1 ⋆ q ≡ q
1⋆q≡q q = ·-identityˡ q

sucn⋆q≡n⋆q+q : (n : ℕ)(q : ℚ) → (suc n) ⋆ q ≡ (n ⋆ q) + q
sucn⋆q≡n⋆q+q n q = (λ i → path n i · q) ∙ helper3ℚ ([ pos n , 1 ]) q
  where path : (n : ℕ) → [ pos (suc n) , 1 ] ≡ 1 + [ pos n , 1 ]
        path n = eq/ _ _ (helper2 (pos n))

sucn⋆q>0 : (n : ℕ)(q : ℚ) → q > 0 → (suc n) ⋆ q > 0
sucn⋆q>0 zero q q>0 = subst (_> 0) (sym (1⋆q≡q q)) q>0
sucn⋆q>0 (suc n) q q>0 = subst (_> 0) (sym (sucn⋆q≡n⋆q+q (suc n) q))
  (+-Pres>0 {x = suc n ⋆ q} (sucn⋆q>0 n q q>0) q>0)

n⋆q≥0 : (n : ℕ)(q : ℚ) → q > 0 → n ⋆ q ≥ 0
n⋆q≥0 zero q _ = inr (sym (0⋆q≡0 q))
n⋆q≥0 (suc n) q q>0 = inl (sucn⋆q>0 n q q>0)


-- Archimedean-ness of ℚ

private
  archimedes-helper : (x y : ℤ × ℕ₊₁) → [ y ] > 0 → Σ[ n ∈ ℕ ] n ⋆ [ y ] > [ x ]
  archimedes-helper (a , b) (c , d) y>0 =
    let right = (-1 ·ℤ a) ·ℤ (1 ·ℤ ℕ₊₁→ℤ d)
        c>0 = transport (sym (>0≡>0r [ c , d ])) y>0
        (n , ->-) =
          archimedesℤ right (c ·ℤ ℕ₊₁→ℤ b)
            (·ℤ-Pres>0 {x = c} {y = ℕ₊₁→ℤ b} c>0 (ℕ₊₁→ℤ>0 b))
    in  n , subst (λ t → t +ℤ right >ℤ 0) (helper1 (pos n) c (ℕ₊₁→ℤ b)) ->-

∥archimedes∥ : (q ε : ℚ) → ε > 0 → ∥ Σ[ n ∈ ℕ ] n ⋆ ε > q ∥
∥archimedes∥ = SetQuot.elimProp2 (λ _ _ → isPropΠ (λ _ → squash))
  (λ x y h → ∣ archimedes-helper x y h ∣)

archimedes : (q ε : ℚ) → ε > 0 → Σ[ n ∈ ℕ ] n ⋆ ε > q
archimedes q ε ε>0 = case-split (dec< q (zero ⋆ ε))
  where
  case-split : Dec (zero ⋆ ε > q) → Σ[ n ∈ ℕ ] n ⋆ ε > q
  case-split (yes p) = zero , p
  case-split (no ¬p) = find (λ n → isProp< {x = q} {y = n ⋆ ε})
    (λ n → dec< q (n ⋆ ε)) ¬p (∥archimedes∥ q ε ε>0)
