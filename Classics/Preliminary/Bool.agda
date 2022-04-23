{-

This file contains some facts about Bool so far not included in the Cubical Standard Library.

-}
{-# OPTIONS --safe #-}
module Classics.Preliminary.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum


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

-- Cancellation

and-cancelˡ : ∀ x y → x and y ≡ true → x ≡ true
and-cancelˡ true  true  _ = refl
and-cancelˡ true  false _ = refl
and-cancelˡ false true  p = Empty.rec (false≢true p)
and-cancelˡ false false p = Empty.rec (false≢true p)

and-cancelʳ : ∀ x y → x and y ≡ true → y ≡ true
and-cancelʳ true  true  _ = refl
and-cancelʳ true  false p = Empty.rec (false≢true p)
and-cancelʳ false true  _ = refl
and-cancelʳ false false p = Empty.rec (false≢true p)

and-forceˡ : ∀ x y → x and y ≡ false → x ≡ true → y ≡ false
and-forceˡ true  true  p _ = Empty.rec (true≢false p)
and-forceˡ true  false _ _ = refl
and-forceˡ false true  _ q = Empty.rec (false≢true q)
and-forceˡ false false _ _ = refl

and-forceʳ : ∀ x y → x and y ≡ false → y ≡ true → x ≡ false
and-forceʳ true  true  p _ = Empty.rec (true≢false p)
and-forceʳ true  false _ q = Empty.rec (false≢true q)
and-forceʳ false true  _ _ = refl
and-forceʳ false false _ _ = refl

-- Absorption

and-absorpˡ : ∀ x y → x ≡ false → x and y ≡ false
and-absorpˡ true  true  p = Empty.rec (true≢false p)
and-absorpˡ true  false _ = refl
and-absorpˡ false true  _ = refl
and-absorpˡ false false _ = refl

-- Dichotomy

or-dichotomy : ∀ x y → x or y ≡ true → (x ≡ true) ⊎ (y ≡ true)
or-dichotomy true _ _ = inl refl
or-dichotomy false true _ = inr refl
or-dichotomy false false p = Empty.rec (false≢true p)

or≡true : ∀ x y → (x ≡ true) ⊎ (y ≡ true) → x or y ≡ true
or≡true true  true  _ = refl
or≡true true  false _ = refl
or≡true false true  _ = refl
or≡true false false (inl p) = Empty.rec (false≢true p)
or≡true false false (inr p) = Empty.rec (false≢true p)
