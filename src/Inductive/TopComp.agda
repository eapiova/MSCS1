
{-# OPTIONS --safe #-}

module Inductive.TopComp where

open import Inductive.Prelude
open import Data.Nat using (ℕ)
open import Data.List.Base using ([])

open import Inductive.Syntax
open import Inductive.Context
open import Inductive.Evaluation
open import Inductive.Derivability
open import Inductive.Computability

compFTopClosed : {n : ℕ} -> Computable n (isType [] tyTop)
compFTopClosed =
  compTyClosedTop
    (fTop wfNil)
    evalTop
    (reflTy (fTop wfNil))

compITopClosed : {n : ℕ} -> Computable n (hasTy [] tmStar tyTop)
compITopClosed =
  compTmClosedTop
    (iTop wfNil)
    compFTopClosed
    evalTop
    evalStar
    (reflTm (iTop wfNil))

compCTopClosed : {n : ℕ} {t : RawTerm}
  -> Computable n (hasTy [] t tyTop)
  -> Computable n (termEq [] t tmStar tyTop)
compCTopClosed comp@(compTmClosedTop d _ evA evt _) =
  compTmEqClosedTop
    (cTop d)
    comp
    compITopClosed
    evA
    evt
    evalStar
