open import Classical.Axioms
open import Classical.Axioms.Resizing
module Solver.Classical (decide : LEM) where
open import Solver.Formula
open Models

open import Classical.Preliminary.DecidablePropositions

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_; const)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Bool

private variable
  n : ℕ

computeProp : (F : Formula (Fin n))
  → {Bool→Type (binFoldBool (_⊨ F))}
  → (P : FinVec (hProp ℓ-zero) n)
  → (fst ∘ P) ⊢ F
computeProp F {witness} P = computeDec F {witness} (hProp→DecProp decide ∘ P)

computePropℓ : ∀ {ℓ} (F : Formula (Fin n))
  → {Bool→Type (binFoldBool (_⊨ F))}
  → (P : FinVec (hProp ℓ) n)
  → (fst ∘ P) ⊢ F
computePropℓ F {witness} P = {! ? !}

private module test (P Q R : Type) (pP : isProp P) (pQ : isProp Q) (pR : isProp R) where
  open import Cubical.Data.Sigma
    using (_×_)
  open import Cubical.Data.Sum
    using (_⊎_)
  open import Cubical.Relation.Nullary.Base
    using (¬_; ∥_∥)
  
  _↔_ : Type → Type → Type
  P ↔ Q = (P → Q) × (Q → P)

  infix 0 _∥⊎∥_
  _∥⊎∥_ : Type → Type → Type
  P ∥⊎∥ Q = ∥ P ⊎ Q ∥

  open import Cubical.Data.Fin.Literals
  test : (P × Q → R) ↔ (P → ¬ Q ∥⊎∥ R)
  test = computeProp
    ((p ∧ᶠ q →ᶠ r) ↔ᶠ (p →ᶠ ¬ᶠ q ∨ᶠ r))
    ((P , pP) ∷ (Q , pQ) ∷ (R , pR) ∷ [])
    where
      p q r : Formula (Fin 3)
      p = 0 ᶠ
      q = 1 ᶠ
      r = 2 ᶠ
