{-

A useful lemma for induction

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level


InhabMin : (ℕ → Type ℓ) → Type ℓ
InhabMin P = Σ[ n ∈ ℕ ] P (suc n) × ((m : ℕ) → m ≤ n → ¬ P m)


module _
  {P : ℕ → Type ℓ}
  (isPropP : (n : ℕ) → isProp (P n))
  where

  private
    inhab-path : (x y : InhabMin P) → x .fst ≡ y .fst
    inhab-path x y with x .fst ≟ y .fst
    ... | lt x<y = Empty.rec (y .snd .snd _ x<y (x .snd .fst))
    ... | eq x≡y = x≡y
    ... | gt x>y = Empty.rec (x .snd .snd _ x>y (y .snd .fst))

  isPropInhabMin : isProp (InhabMin P)
  isPropInhabMin x y i .fst = inhab-path x y i
  isPropInhabMin x y i .snd .fst =
    isProp→PathP (λ i → isPropP (suc (inhab-path x y i)))
    (x .snd .fst) (y .snd .fst) i
  isPropInhabMin x y i .snd .snd =
    isProp→PathP (λ i → isPropΠ3 {B = λ m → m ≤ inhab-path x y i} (λ _ _ _ → isProp⊥))
    (x .snd .snd) (y .snd .snd) i


  module _
    (decP : (n : ℕ) → Dec (P n))
    (¬p₀ : ¬ P zero)
    where

    private
      module _ (n₀ : ℕ)(p₀ : P n₀) where

        type-helper-zero : (m : ℕ) → m ≤ 0 → ¬ P m
        type-helper-zero zero _ = ¬p₀
        type-helper-zero (suc m) m≤0 _ = ¬-<-zero m≤0

        type-helper-ind : (n : ℕ) → ((m : ℕ) → m ≤ n → ¬ P m)
          → ¬ P (suc n) → (m : ℕ) → m ≤ suc n → ¬ P m
        type-helper-ind n f ¬psuc m m≤sucn with m ≟ suc n
        ... | lt m<sucn = f m (pred-≤-pred m<sucn)
        ... | eq m≡sucn = transport (λ i → ¬ P (m≡sucn (~ i))) ¬psuc
        ... | gt m>sucn = Empty.rec (<-asym m>sucn m≤sucn)

        type-helper : (n : ℕ) → ((m : ℕ) → m ≤ n → ¬ P m) ⊎ InhabMin P
        type-helper zero = inl type-helper-zero
        type-helper (suc n) with type-helper n | decP (suc n)
        ... | inl f | yes p = inr (n , p , f)
        ... | inl f | no ¬p = inl (type-helper-ind _ f ¬p)
        ... | inr m | _     = inr m

        find-helper : InhabMin P
        find-helper with type-helper n₀
        ... | inl f = Empty.rec (f _ ≤-refl p₀)
        ... | inr m = m


    findMin : ∥ Σ[ n ∈ ℕ ] P n ∥ → InhabMin P
    findMin = Prop.rec isPropInhabMin (λ (n , p) → find-helper n p)

    findInterval : ∥ Σ[ n ∈ ℕ ] P n ∥ → Σ[ n ∈ ℕ ] (¬ P n) × P (suc n)
    findInterval p .fst = findMin p .fst
    findInterval p .snd .fst = findMin p .snd .snd _ ≤-refl
    findInterval p .snd .snd = findMin p .snd .fst


  module _
    (decP : (n : ℕ) → Dec (P n))
    where

    find : ∥ Σ[ n ∈ ℕ ] P n ∥ → Σ[ n ∈ ℕ ] P n
    find ∃p with decP 0
    ... | yes p = 0 , p
    ... | no ¬p = let (n , p , h) = findMin decP ¬p ∃p in suc n , p


{-

  Find under LEM

-}

open import Classical.Axioms.ExcludedMiddle

module FindByOracle (decide : LEM) where

  findByOracle :
    {P : ℕ → Type ℓ}
    (isPropP : (n : ℕ) → isProp (P n))
    → ∥ Σ[ n ∈ ℕ ] P n ∥ → Σ[ n ∈ ℕ ] P n
  findByOracle isPropP = find isPropP (λ n → decide (isPropP n))


{-

  Lemmas for Conveniently Induction on ≤

-}

≤-ind : {m n : ℕ} → m ≤ suc n → (m ≤ n) ⊎ (m ≡ suc n)
≤-ind {m = m} {n = n} m≤sn = case-split (≤-split m≤sn)
  where
  case-split : (m < suc n) ⊎ (m ≡ suc n) → _
  case-split (inl sm≤sn) = inl (pred-≤-pred sm≤sn)
  case-split (inr m≡sn) = inr m≡sn

<≤-split : (m n : ℕ) → (m < n) ⊎ (m ≥ n)
<≤-split m n = case-split (m ≟ n)
  where
  case-split : Trichotomy m n → _
  case-split (lt m<n) = inl m<n
  case-split (eq m≡n) = inr (_ , sym m≡n)
  case-split (gt m>n) = inr (<-weaken m>n)


{-

  A Variant of Maximum

-}

sucmax : (m n : ℕ) → ℕ
sucmax m n = suc (max m n)

sucmax>left : {m n : ℕ} → sucmax m n > m
sucmax>left = ≤<-trans left-≤-max ≤-refl

sucmax>right : {m n : ℕ} → sucmax m n > n
sucmax>right = ≤<-trans right-≤-max ≤-refl
