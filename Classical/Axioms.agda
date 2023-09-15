{-# OPTIONS --safe #-}
module Classical.Axioms where

open import Cubical.Foundations.Prelude

open import Classical.Axioms.Choice public
open import Classical.Axioms.ExcludedMiddle public
open import Classical.Axioms.Diaconescu

-- We record up axioms to make use of Agda's instance argument,
-- so no one needs to write them everywhere explicitly.

----------------------------------------------

-- In Oracle's realm, 🤖 stands with pride,
-- An honored member by logic's side,
-- Holding truths, h-propositions untold,
-- In legal terms, its wisdom unfolds.

-- To summon 🤖, in your code's embrace,
-- `module _ ⦃ 🤖 : Oracle ⦄` takes its place,
-- `open Oracle 🤖,` the function you'll find,
-- In the library's scripts, it's logic's mind.

-- Short and sweet, this tale of 🤖's grace,
-- In the world of Oracle, it finds its place.

-- by ChatGPT

----------------------------------------------

-- Examples are almost all files in this library.


record Oracle : Typeω where
  field
    decide : LEM

----------------------------------------------

-- Warning:

-- In Oracle's realm, 🤖, a cryptic sage,
-- Knows all the truths of every age,
-- Yet in its wisdom, often it won't tell,
-- The mysteries it guards, it keeps so well.

-- still by ChatGPT

----------------------------------------------

record MegaPicker : Typeω where
  field
    choose : AC

  decide : LEM
  decide = AC→LEM choose
