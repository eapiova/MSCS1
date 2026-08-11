
{-# OPTIONS --safe #-}

module Inductive.EqComp where

open import Inductive.Prelude
open import Data.Nat using (ℕ)
open import Data.List.Base using ([])

open import Inductive.Syntax
open import Inductive.Context
open import Inductive.Evaluation
open import Inductive.Derivability
open import Inductive.Computability
open import Inductive.Inversion
open import Inductive.Presupposition
open import Inductive.Structural

compFEqClosed : {n : ℕ} {A : RawType} {a b : RawTerm}
  -> Computable n (isType [] A)
  -> Computable n (hasTy [] a A)
  -> Computable n (hasTy [] b A)
  -> Computable n (isType [] (tyEq A a b))
compFEqClosed compA compa compb =
  compTyClosedEq
    (fEq (compToDerivable compA) (compToDerivable compa) (compToDerivable compb))
    evalEq
    (reflTy (fEq (compToDerivable compA) (compToDerivable compa) (compToDerivable compb)))
    compA
    compa
    compb

compIEqClosed : {n : ℕ} {A : RawType} {a : RawTerm}
  -> Computable n (hasTy [] a A)
  -> Computable n (hasTy [] tmRefl (tyEq A a a))
compIEqClosed compa =
  compTmClosedEq
    (iEq (compToDerivable compa))
    (compFEqClosed (compTmToCompTy compa) compa compa)
    evalEq
    evalRefl
    (reflTm (iEq (compToDerivable compa)))
    (compReflTmClosed compa)

compEEqClosed : {n : ℕ} {A : RawType} {a b p : RawTerm}
  -> Computable n (hasTy [] p (tyEq A a b))
  -> Computable n (termEq [] a b A)
compEEqClosed {A = A} {a = a} {b = b}
  (compTmClosedEq _ _ (evalEq {A = A} {a = a} {b = b}) _ _ compab) =
  compab

compCEqClosed : {n : ℕ} {A : RawType} {a b p : RawTerm}
  -> Computable n (hasTy [] p (tyEq A a b))
  -> Computable n (termEq [] p tmRefl (tyEq A a b))
compCEqClosed {A = A} {a = a} {b = b}
  compp@(compTmClosedEq dp compEqTy (evalEq {A = A} {a = a} {b = b}) evp _ compab) =
  compTmEqClosedEq
    (cEq dp dA da db)
    compp
    compEqRefl
    evalEq
    evp
    evalRefl
    compab
  where
  compa : Computable _ (hasTy [] a A)
  compa = compTmEqLeft compab

  dA : Derivable (isType [] A)
  dA = compToDerivable (compTmToCompTy compa)

  da : Derivable (hasTy [] a A)
  da = compToDerivable compa

  db : Derivable (hasTy [] b A)
  db = assocTmRight (compToDerivable compab)

  dEqTy : Derivable (typeEq [] (tyEq A a a) (tyEq A a b))
  dEqTy = fEqEq (reflTy dA) (reflTm da) (compToDerivable compab)

  dEqRefl : Derivable (hasTy [] tmRefl (tyEq A a b))
  dEqRefl = conv (iEq da) dEqTy

  compEqRefl : Computable _ (hasTy [] tmRefl (tyEq A a b))
  compEqRefl =
    compTmClosedEq
      dEqRefl
      compEqTy
      evalEq
      evalRefl
      (cEq dEqRefl dA da db)
      compab
