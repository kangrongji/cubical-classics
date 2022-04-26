{-# OPTIONS -W ignore #-}
module Solver.Formula where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_; const)
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty
  renaming (rec to rec⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
  using (_⊎_; inl; inr)
  renaming (rec to rec⊎; map to map⊎)
open import Cubical.HITs.PropositionalTruncation
  using (∣_∣; squash; isPropPropTrunc)
  renaming (map to map∥∥)
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Classical.Preliminary.Bool

private variable
  ℓ ℓ' : Level

module _ where -- Stuff that should be in other modules
  Dec¬ : {P : Type ℓ}
    → Dec P → Dec (¬ P)
  Dec¬ (yes p) = no (λ z → z p)
  Dec¬ (no ¬p) = yes ¬p

  Dec× : {P : Type ℓ} {Q : Type ℓ'}
    → Dec P → Dec Q → Dec (P × Q)
  Dec× (yes p) (yes q) = yes (p , q)
  Dec× (yes p) (no ¬q) = no λ z → ¬q (snd z)
  Dec× (no ¬p) _       = no λ z → ¬p (fst z)

  Dec⊎ : {P : Type ℓ} {Q : Type ℓ'}
    → Dec P → Dec Q → Dec (P ⊎ Q)
  Dec⊎ (yes p) _       = yes (inl p)
  Dec⊎ (no ¬p) (yes q) = yes (inr q)
  Dec⊎ (no ¬p) (no ¬q) = no (rec⊎ ¬p ¬q)

  -- We might try to do a DecΠ, but that's slightly more complicated.
  Dec→ : {P : Type ℓ} {Q : Type ℓ'}
    → Dec P → Dec Q → Dec (P → Q)
  Dec→ _       (yes q) = yes λ _ → q
  Dec→ (yes p) (no ¬q) = no λ z → ¬q (z p)
  Dec→ (no ¬p) (no ¬q) = yes λ p → rec⊥ (¬p p)

  Bool→Type∥⊎∥' : (a b : Bool) → ∥ Bool→Type a ⊎ Bool→Type b ∥ → Bool→Type (a or b)
  Bool→Type∥⊎∥' true  false ∣ _ ∣ = tt
  Bool→Type∥⊎∥' true  true  ∣ _ ∣ = tt
  Bool→Type∥⊎∥' false true  ∣ _ ∣ = tt
  Bool→Type∥⊎∥' false false ∣ inl () ∣
  Bool→Type∥⊎∥' false false ∣ inr () ∣
  Bool→Type∥⊎∥' a b (squash r₁ r₂ i)
    = isPropBool→Type (Bool→Type∥⊎∥' a b r₁) (Bool→Type∥⊎∥' a b r₂) i

infixr 35 ¬ᶠ_
infixl 34 _∧ᶠ_ _∨ᶠ_
infixl 33 _↔ᶠ_
infixr 33 _→ᶠ_
infix 100 _ᶠ
data Formula (a : Type) : Type where
  _ᶠ : (ϕ : a) → Formula a
  ⊤ᶠ ⊥ᶠ : Formula a
  ¬ᶠ_ : (F : Formula a) → Formula a
  _∧ᶠ_ _∨ᶠ_ _→ᶠ_ _↔ᶠ_ : (F G : Formula a) → Formula a

private module _ {a : Type} where
  infix 30 _⊢_
  _⊢_ : (a → Type ℓ) → Formula a → Type ℓ
  Γ ⊢ (ϕ ᶠ) = Γ ϕ
  Γ ⊢ ⊤ᶠ = Unit*
  Γ ⊢ ⊥ᶠ = ⊥*
  Γ ⊢ (¬ᶠ F) = ¬ Γ ⊢ F
  Γ ⊢ (F ∧ᶠ G) = Γ ⊢ F × Γ ⊢ G
  Γ ⊢ (F ∨ᶠ G) = ∥ Γ ⊢ F ⊎ Γ ⊢ G ∥
  Γ ⊢ (F →ᶠ G) = Γ ⊢ F → Γ ⊢ G
  Γ ⊢ (F ↔ᶠ G) = (Γ ⊢ F → Γ ⊢ G) × (Γ ⊢ G → Γ ⊢ F)

  isProp⊢ : {Γ : a → Type ℓ}
    → (∀ a → isProp (Γ a))
    → (F : Formula a) → isProp (Γ ⊢ F)
  isProp⊢ Γ (ϕ ᶠ) = Γ ϕ
  isProp⊢ Γ ⊤ᶠ = isPropUnit*
  isProp⊢ Γ ⊥ᶠ = isProp⊥*
  isProp⊢ Γ (¬ᶠ F) = isProp¬ _
  isProp⊢ Γ (F ∧ᶠ G) = isProp× (isProp⊢ Γ F) (isProp⊢ Γ G)
  isProp⊢ Γ (F ∨ᶠ G) = isPropPropTrunc
  isProp⊢ Γ (F →ᶠ G) = isPropΠ λ _ → isProp⊢ Γ G
  isProp⊢ Γ (F ↔ᶠ G) =
    isProp× (isPropΠ λ _ → isProp⊢ Γ G) (isPropΠ λ _ → isProp⊢ Γ F)

  Dec⊢ : {Γ : a → Type ℓ}
    → (∀ a → Dec (Γ a))
    → (F : Formula a) → Dec (Γ ⊢ F)
  Dec⊢ Γ (ϕ ᶠ) = Γ ϕ
  Dec⊢ Γ ⊤ᶠ = yes tt*
  Dec⊢ Γ ⊥ᶠ = no lower
  Dec⊢ Γ (¬ᶠ F) = Dec¬ (Dec⊢ Γ F)
  Dec⊢ Γ (F ∧ᶠ G) = Dec× (Dec⊢ Γ F) (Dec⊢ Γ G)
  Dec⊢ Γ (F ∨ᶠ G) = Dec∥∥ (Dec⊎ (Dec⊢ Γ F) (Dec⊢ Γ G))
  Dec⊢ Γ (F →ᶠ G) = Dec→ (Dec⊢ Γ F) (Dec⊢ Γ G)
  Dec⊢ Γ (F ↔ᶠ G) = Dec× (Dec→ (Dec⊢ Γ F) (Dec⊢ Γ G)) (Dec→ (Dec⊢ Γ G) (Dec⊢ Γ F))

  _⊨_ : (a → Bool) → Formula a → Bool
  Γ ⊨ (ϕ ᶠ) = Γ ϕ
  Γ ⊨ ⊤ᶠ = true
  Γ ⊨ ⊥ᶠ = false
  Γ ⊨ (¬ᶠ F) = not (Γ ⊨ F)
  Γ ⊨ (F ∧ᶠ G) = Γ ⊨ F and Γ ⊨ G
  Γ ⊨ (F ∨ᶠ G) = Γ ⊨ F or Γ ⊨ G
  Γ ⊨ (F →ᶠ G) = not (Γ ⊨ F) or (Γ ⊨ G)
  Γ ⊨ (F ↔ᶠ G) = not (Γ ⊨ F) ⊕ (Γ ⊨ G)
    -- A strange case where  (not p) ⊕ q = not (p ⊕ q)

  abstract  -- Since they are proved to be propositions, we don't need the details.
    Sound : (Γ : a → Bool) (F : Formula a)
      → Bool→Type (Γ ⊨ F) → (Bool→Type ∘ Γ) ⊢ F
    Complete : (Γ : a → Bool) (F : Formula a)
      → (Bool→Type ∘ Γ) ⊢ F → Bool→Type (Γ ⊨ F)

    Sound Γ (ϕ ᶠ) t = t
    Sound Γ ⊤ᶠ t = tt*
    Sound Γ (¬ᶠ F) t u with Γ ⊨ F | Complete Γ F u
    ... | false | ()
    Sound Γ (F ∧ᶠ G) t with Γ ⊨ F | Γ ⊨ G | Sound Γ F | Sound Γ G
    ... | true  | true  | f | g = f tt , g tt
    ... | false | false | _ | _ = Cubical.Data.Empty.rec t
      -- ^ This case is needed to hint Agda's case splitting system
    Sound Γ (F ∨ᶠ G) t with Γ ⊨ F | Γ ⊨ G | Sound Γ F | Sound Γ G
    ... | true | true | f | g = ∣ inl (f tt) ∣
    ... | false | true | f | g = ∣ inr (g tt) ∣
    ... | true | false | f | g = ∣ inl (f tt) ∣
    Sound Γ (F →ᶠ G) t u with Γ ⊨ F | Γ ⊨ G | Complete Γ F | Sound Γ G
    ... | false | false | f | g = g (f u)
    ... | false | true  | f | g = g tt
    ... | true  | true  | f | g = g tt
    Sound Γ (F ↔ᶠ G) t with Γ ⊨ F | Γ ⊨ G
      | Sound Γ F | Complete Γ F | Sound Γ G | Complete Γ G
    ... | false | false | fˢ | fᶜ | gˢ | gᶜ = (gˢ ∘ fᶜ) , (fˢ ∘ gᶜ)
    ... | true  | true  | fˢ | fᶜ | gˢ | gᶜ = (gˢ ∘ fᶜ) , (fˢ ∘ gᶜ)

    Complete Γ (ϕ ᶠ) t = t
    Complete Γ ⊤ᶠ t = tt
    Complete Γ (¬ᶠ F) t with Γ ⊨ F | Sound Γ F
    ... | false | f = tt
    ... | true | f = t (f tt)
    Complete Γ (F ∧ᶠ G) (f , g) with Γ ⊨ F | Γ ⊨ G | Complete Γ F f | Complete Γ G g
    ... | true | true | _ | _ = tt
    Complete Γ (F ∨ᶠ G) t = -- Special treatment for the truncation
      Bool→Type∥⊎∥' _ _ (map∥∥ (map⊎ (Complete Γ F) (Complete Γ G)) t)
    Complete Γ (F →ᶠ G) t with Γ ⊨ F | Γ ⊨ G | Sound Γ F | Complete Γ G
    ... | false | false | _ | _ = tt
    ... | false | true  | _ | _ = tt
    ... | true  | true  | _ | _ = tt
    ... | true  | false | f | g = g (t (f tt))
    Complete Γ (F ↔ᶠ G) t with Γ ⊨ F | Γ ⊨ G
      | Sound Γ F | Complete Γ F | Sound Γ G | Complete Γ G
    ... | false | false | fˢ | fᶜ | gˢ | gᶜ = tt
    ... | false | true  | fˢ | fᶜ | gˢ | gᶜ = fᶜ (snd t (gˢ tt))
    ... | true  | false | fˢ | fᶜ | gˢ | gᶜ = gᶜ (fst t (fˢ tt))
    ... | true  | true  | fˢ | fᶜ | gˢ | gᶜ = tt

-- Next, we put the automation to use.

open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
  using (Fin; fzero; fsuc; ¬Fin0; fsplit)
  renaming (elim to elimFin)
FinVec : Type ℓ → ℕ → Type ℓ
FinVec A n = Fin n → A
module _ {A : Type ℓ} where -- Should also be in agda-cubical
  [] : FinVec A 0
  [] = rec⊥ ∘ ¬Fin0

  _∷_ : {n : ℕ} → A → FinVec A n → FinVec A (1 + n)
  (a ∷ v) i with fsplit i
  ... | inl _ = a
  ... | inr (j , _) = v j

  FinVecNil : (v : FinVec A 0) → [] ≡ v
  FinVecNil v i r with ¬Fin0 r
  ... | ()

  FinVecCon : ∀ {n} → (v : FinVec A (1 + n))
    → v fzero ∷ (v ∘ fsuc) ≡ v
  FinVecCon {n} v = funExt helper
    where
      helper : (i : Fin (suc n)) → (v fzero ∷ (v ∘ fsuc)) i ≡ v i
      helper i with fsplit i
      ... | inl fzero≡i = cong v fzero≡i
      ... | inr (j , fsucj≡i) = cong v fsucj≡i

  elimFinVec : (P : ∀ {n} → FinVec A n → Type ℓ')
    → P [] → (∀ {k} a (v : FinVec A k) → P v → P (a ∷ v))
    → ∀ {n} (v : FinVec A n) → P v
  elimFinVec P nil con {zero} v = subst P (FinVecNil v) nil
  elimFinVec P nil con {suc n} v = subst P (FinVecCon v)
    (con (v fzero) (v ∘ fsuc) (elimFinVec P nil con (v ∘ fsuc)))

module NbE where
  private variable
    n : ℕ
  binFoldBool : (FinVec Bool n → Bool) → Bool
  binFoldBool {zero} α = α []
  binFoldBool {suc n} α
    = binFoldBool (λ τ → α (false ∷ τ))
    and binFoldBool (λ τ → α (true ∷ τ))

  binFoldCorrect :
      (Γ : FinVec Bool n)
    → (α : FinVec Bool n → Bool)
    → Bool→Type (binFoldBool α)
    → Bool→Type (α Γ)
  binFoldCorrect
    = elimFinVec (λ Γ → ∀ α → (Bool→Type (binFoldBool α)) → Bool→Type (α Γ))
      (λ α z → z) auxCon
    where
      auxCon : {k : ℕ} (a : Bool) (v : FinVec Bool k)
        → (∀ α → Bool→Type (binFoldBool α) → Bool→Type (α v))
        → ∀ α → Bool→Type (binFoldBool α) → Bool→Type (α (a ∷ v))
      auxCon a v IH α H with a | -- Make a sneaky use of our lemma
        Sound (λ b → binFoldBool (λ τ → α (b ∷ τ))) (false ᶠ ∧ᶠ true ᶠ) H
      ... | true  | (pfalse , ptrue) = IH _ ptrue
      ... | false | (pfalse , ptrue) = IH _ pfalse

  computeBool : (F : Formula (Fin n))
    → {Bool→Type (binFoldBool (_⊨ F))}
    → (P : FinVec Bool n)
    → (Bool→Type ∘ P) ⊢ F
  computeBool F {witness} P = Sound P F (binFoldCorrect P (_⊨ F) witness)


