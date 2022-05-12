{-

  Archimedean-ness of Ordered Ring

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedRing.Archimedes where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Nullary

open import Classical.Preliminary.Nat
open import Classical.Algebra.OrderedRing

private
  variable
    ℓ ℓ' : Level


module _ (𝓡 : OrderedRing ℓ ℓ') where

  private
    R = 𝓡 .fst .fst

  open CommRingStr   (𝓡 .fst .snd)
  open OrderedRingStr 𝓡


  -- We have two versions of Archimedean-ness.
  -- The un-truncated version is seemingly much stronger than the truncated version,
  -- but they turn out to be equivalent.

  isArchimedean : Type (ℓ-max ℓ ℓ')
  isArchimedean = (q ε : R) → ε > 0r → Σ[ n ∈ ℕ ] n ⋆ ε > q

  isArchimedean∥∥ : Type (ℓ-max ℓ ℓ')
  isArchimedean∥∥ = (q ε : R) → ε > 0r → ∥ Σ[ n ∈ ℕ ] n ⋆ ε > q ∥


  -- The equivalence, and one-side is rather trivial.

  isArchimedean→isArchimedean∥∥ : isArchimedean → isArchimedean∥∥
  isArchimedean→isArchimedean∥∥ archimedes q ε ε>0 = ∣ archimedes q ε ε>0 ∣

  isArchimedean∥∥→isArchimedean : isArchimedean∥∥ → isArchimedean
  isArchimedean∥∥→isArchimedean ∥archimedes∥ q ε ε>0 = case-split (trichotomy q 0r)
    where
    case-split : Trichotomy q 0r → _
    case-split (lt q<0) = 0 , subst (_> q) (sym (0⋆q≡0 ε)) q<0
    case-split (eq q≡0) = 1 , transport (λ i → 1⋆q≡q ε (~ i) > q≡0 (~ i)) ε>0
    case-split (gt q>0) = find (λ _ → isProp<) (λ _ → dec< _ _)
      (<-asym (subst (_< q) (sym (0⋆q≡0 ε)) q>0)) (∥archimedes∥ q ε ε>0)
