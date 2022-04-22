{-

This file contains some facts about Bool so far not included in the Cubical Standard Library.

-}
{-# OPTIONS --safe #-}
module Classics.Preliminary.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool.Base
open import Cubical.Data.Empty

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

private
  variable
    ℓ : Level

-- Algebraic properties of `and` operation

and-zeroˡ : ∀ x → false and x ≡ false
and-zeroˡ false = refl
and-zeroˡ true  = refl

and-zeroʳ : ∀ x → x and false ≡ false
and-zeroʳ false = refl
and-zeroʳ true  = refl

and-identityˡ : ∀ x → true and x ≡ x
and-identityˡ false = refl
and-identityˡ true  = refl

and-identityʳ : ∀ x → x and true ≡ x
and-identityʳ false = refl
and-identityʳ true  = refl

and-comm : ∀ x y → x and y ≡ y and x
and-comm true  true  = refl
and-comm true  false = refl
and-comm false true  = refl
and-comm false false = refl

and-assoc : ∀ x y z → x and (y and z) ≡ (x and y) and z
and-assoc true  true  true  = refl
and-assoc true  true  false = refl
and-assoc true  false true  = refl
and-assoc true  false false = refl
and-assoc false true  true  = refl
and-assoc false true  false = refl
and-assoc false false true  = refl
and-assoc false false false = refl

and-idem : ∀ x → x and x ≡ x
and-idem false = refl
and-idem true  = refl

-- Absorption laws

or-and-absorp : ∀ x y → x or (x and y) ≡ x
or-and-absorp true  true  = refl
or-and-absorp true  false = refl
or-and-absorp false true  = refl
or-and-absorp false false = refl

and-or-absorp : ∀ x y → x and (x or y) ≡ x
and-or-absorp true  true  = refl
and-or-absorp true  false = refl
and-or-absorp false true  = refl
and-or-absorp false false = refl

-- Distribution laws

or-and-dist : ∀ x y z → x or (y and z) ≡ (x or y) and (x or z)
or-and-dist true  true  true  = refl
or-and-dist true  true  false = refl
or-and-dist true  false true  = refl
or-and-dist true  false false = refl
or-and-dist false true  true  = refl
or-and-dist false true  false = refl
or-and-dist false false true  = refl
or-and-dist false false false = refl

and-or-dist : ∀ x y z → x and (y or z) ≡ (x and y) or (x and z)
and-or-dist true  true  true  = refl
and-or-dist true  true  false = refl
and-or-dist true  false true  = refl
and-or-dist true  false false = refl
and-or-dist false true  true  = refl
and-or-dist false true  false = refl
and-or-dist false false true  = refl
and-or-dist false false false = refl

-- Complementation laws

or-compt : ∀ x → x or (not x) ≡ true
or-compt true  = refl
or-compt false = refl

and-compt : ∀ x → x and (not x) ≡ false
and-compt true  = refl
and-compt false = refl

-- de Morgan laws

or-and-deMorgan : ∀ x y → (not x) or (not y) ≡ not (x and y)
or-and-deMorgan true  true  = refl
or-and-deMorgan true  false = refl
or-and-deMorgan false true  = refl
or-and-deMorgan false false = refl

and-or-deMorgan : ∀ x y → (not x) and (not y) ≡ not (x or y)
and-or-deMorgan true  true  = refl
and-or-deMorgan true  false = refl
and-or-deMorgan false true  = refl
and-or-deMorgan false false = refl
