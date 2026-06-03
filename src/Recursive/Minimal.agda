{-# OPTIONS --safe #-}

module Recursive.Minimal where

open import Recursive.Minimal.Base public
open import Recursive.Minimal.Renaming public
open import Recursive.Minimal.Substitution public using
  ( minSubst ; minSubstTmTy ; minSubstTyEqLeft ; minSubstTyEqRight )
open import Recursive.Minimal.SubstEq public
open import Recursive.Minimal.Reflection public
