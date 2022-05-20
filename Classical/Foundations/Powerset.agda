{-

This file is only used to put everything about powerset together,
so that importing will be more convenient.

-}
{-# OPTIONS --safe #-}
module Classical.Foundations.Powerset where

open import Classical.Axioms.ExcludedMiddle

open import Classical.Foundations.Powerset.Base
open import Classical.Foundations.Powerset.Membership
open import Classical.Foundations.Powerset.Boolean
open import Classical.Foundations.Powerset.Properties
open import Classical.Foundations.Powerset.BigOps
open import Classical.Foundations.Powerset.Finiteness


module Powerset (decide : LEM) where

  open Base         decide  public
  open Membership   decide  public
  open Boolean      decide  public
  open Properties   decide  public
  open BigOps       decide  public
  open Finiteness   decide  public
