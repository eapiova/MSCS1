{-# OPTIONS --safe #-}

module Tait.Minimal where

open import Tait.Minimal.Base public
open import Tait.Minimal.Renaming public
open import Tait.Minimal.Substitution public using
  ( minSubst ; minSubstTmTy ; minSubstTyEqLeft ; minSubstTyEqRight )
open import Tait.Minimal.SubstEq public
open import Tait.Minimal.Reflection public
