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
