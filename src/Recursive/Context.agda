{-# OPTIONS --safe #-}

-- Tait-style rebuild (Phase K/L). Full theory: Top, Sigma, Eq, Qtr.
-- Shared context and judgement-form declarations.

module Recursive.Context where

open import Recursive.Prelude
open import Data.List.Base using (List)

open import Recursive.Syntax

Ctx : Type
Ctx = List RawType

data JForm : Type where
  isType : Ctx -> RawType -> JForm
  typeEq : Ctx -> RawType -> RawType -> JForm
  hasTy  : Ctx -> RawTerm -> RawType -> JForm
  termEq : Ctx -> RawTerm -> RawTerm -> RawType -> JForm

ctxOf : JForm -> Ctx
ctxOf (isType gamma _)   = gamma
ctxOf (typeEq gamma _ _) = gamma
ctxOf (hasTy gamma _ _)  = gamma
ctxOf (termEq gamma _ _ _) = gamma
