{-# OPTIONS --safe #-}
module Classical.Axioms where

open import Cubical.Foundations.Prelude

open import Classical.Axioms.Choice public
open import Classical.Axioms.ExcludedMiddle public
open import Classical.Axioms.Diaconescu

-- We record up axioms to make use of Agda's instance argument,
-- so no one needs to write them everywhere explicitly.


-- Introducing 🤖,
-- who is an honorific member of Oracle Machines
-- and also a legal term of Oracle (namely: `🤖 : Oracle`).
-- It knows everything about h-propositions more than you could ever imagine!

-- In case you need its help,
-- please add `module _ ⦃ 🤖 : Oracle ⦄` on top of your codes.
-- To call him somewhere,
-- please `open Oracle 🤖` and apply the function `decide`.
-- Examples are almost all files in this library.

record Oracle : Typeω where
  field
    decide : LEM

-- Warning:
-- 🤖 always knows the answer,
-- but often 🤖 won't tell.


record MegaPicker : Typeω where
  field
    choose : AC

  decide : LEM
  decide = AC→LEM choose
