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

-- Evil syntax
infixr -1 _⅋_
_⅋_ = _∷_
infixl 0 _⟧
_⟧ : ∀ {ℓ}{A : Type ℓ} → A → FinVec A 1
v ⟧ = v ∷ []
infix -2 Solve_⟦_
Solve_⟦_ = computeProp

private module test (P Q R : Type) (pP : isProp P) (pQ : isProp Q) (pR : isProp R) where
  open import Cubical.Data.Sigma
    using (_×_)
  open import Cubical.Data.Sum
    using (_⊎_)
  open import Cubical.HITs.PropositionalTruncation
    using (∥_∥₁)
  open import Cubical.Relation.Nullary.Base
    using (¬_)

  _↔_ : Type → Type → Type
  P ↔ Q = (P → Q) × (Q → P)

  infix 0 _∥⊎∥_
  _∥⊎∥_ : Type → Type → Type
  P ∥⊎∥ Q = ∥ P ⊎ Q ∥₁

  test : (P × Q → R) ↔ (P → ¬ Q ∥⊎∥ R)
  test = Solve (0 ∧ᶠ 1 →ᶠ 2) ↔ᶠ (0 →ᶠ ¬ᶠ 1 ∨ᶠ 2)
    ⟦ P , pP ⅋ Q , pQ ⅋ R , pR ⟧
