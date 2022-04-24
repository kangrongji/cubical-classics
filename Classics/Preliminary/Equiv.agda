{-

Facts about Equivalences

Copied from unreleased new version of cubical std-lib.
Will be abandoned if new release come public.

-}
{-# OPTIONS --safe #-}
module Classics.Preliminary.Equiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function


private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'


precomposesToId→Equiv : (f : A → B) (g : B → A) → f ∘ g ≡ idfun B → isEquiv g → isEquiv f
precomposesToId→Equiv f g id iseqg =  subst isEquiv (sym f-≡-g⁻) (snd (invEquiv (_ , iseqg)))
  where
    g⁻ = invEq (g , iseqg)

    f-≡-g⁻ : _
    f-≡-g⁻ = cong (f ∘_ ) (cong fst (sym (invEquiv-is-linv (g , iseqg)))) ∙ cong (_∘ g⁻) id

isEquiv[f∘equivFunA≃B]→isEquiv[f] : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
                 → (f : B → C) (A≃B : A ≃ B)
                 → isEquiv (f ∘ equivFun A≃B)
                 → isEquiv f
isEquiv[f∘equivFunA≃B]→isEquiv[f] f (g , gIsEquiv) f∘gIsEquiv  =
  precomposesToId→Equiv f _ w w'
    where
      w : f ∘ g ∘ equivFun (invEquiv (_ , f∘gIsEquiv)) ≡ idfun _
      w = (cong fst (invEquiv-is-linv (_ , f∘gIsEquiv)))

      w' : isEquiv (g ∘ equivFun (invEquiv (_ , f∘gIsEquiv)))
      w' = (snd (compEquiv (invEquiv (_ , f∘gIsEquiv) ) (_ , gIsEquiv)))
