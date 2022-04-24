{-

Facts about Integers

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
  renaming (_<_ to _<ℕ_)
open import Cubical.Data.Int
open import Cubical.Data.Unit
open import Cubical.Data.Empty

_<_ : ℤ → ℤ → Type
_<_ (pos m) (pos n) = m <ℕ n
_<_ (pos m) (negsuc n) = ⊥
_<_ (negsuc m) (pos n) = Unit
_<_ (negsuc m) (negsuc n) = n <ℕ m

isProp< : (m n : ℤ) → isProp (m < n)
isProp< (pos m) (pos n) = m≤n-isProp
isProp< (pos m) (negsuc n) = isProp⊥
isProp< (negsuc m) (pos n) = isPropUnit
isProp< (negsuc m) (negsuc n) = m≤n-isProp


